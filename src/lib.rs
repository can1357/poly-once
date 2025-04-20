use core::cell::UnsafeCell;
use core::future::Future;
use core::sync::atomic::{self, AtomicU32, Ordering};
use core::{fmt, mem};

use parking_lot_core::{DEFAULT_PARK_TOKEN, DEFAULT_UNPARK_TOKEN};

/// A thread-safe cell which can be written to only once.
///
/// This structure provides safe initialization for values that might be accessed
/// concurrently by multiple threads. It ensures that the initialization logic
/// runs only once, even if multiple threads attempt to initialize the value simultaneously.
///
/// It uses atomic operations and parking_lot's futex-based synchronization for
/// efficient blocking when necessary.
pub struct Once<T> {
   value: UnsafeCell<mem::MaybeUninit<T>>,
   state: OnceState,
}

impl<T> Once<T> {
   /// Creates a new, uninitialized `Once` cell.
   #[inline]
   #[must_use]
   pub const fn new() -> Self {
      Once {
         state: OnceState::new(),
         value: UnsafeCell::new(mem::MaybeUninit::uninit()),
      }
   }

   /// Creates a new `Once` cell that is already initialized with the given value.
   #[inline]
   #[must_use]
   pub fn with_value(value: T) -> Self {
      Once {
         state: OnceState::done(),
         value: UnsafeCell::new(mem::MaybeUninit::new(value)),
      }
   }

   /// Checks if the cell has been initialized.
   ///
   /// This method never blocks.
   #[inline]
   pub fn is_done(&self) -> bool {
      self.state.is_done(Ordering::Relaxed)
   }

   /// Returns a reference to the contained value if initialized.
   ///
   /// Returns `None` if the cell is uninitialized or currently being initialized.
   /// This method never blocks.
   #[inline]
   pub fn get(&self) -> Option<&T> {
      if self.is_done() {
         // SAFETY: is_done() returned true, so the value is initialized.
         Some(unsafe { self.get_unchecked() })
      } else {
         None
      }
   }

   /// Returns a mutable reference to the contained value if initialized.
   ///
   /// Returns `None` if the cell is uninitialized or currently being initialized.
   /// This method requires exclusive access (`&mut self`) and never blocks.
   #[inline]
   pub fn get_mut(&mut self) -> Option<&mut T> {
      if self.is_done() {
         // SAFETY: is_done() returned true and we have exclusive access (`&mut self`).
         Some(unsafe { self.get_unchecked_mut() })
      } else {
         None
      }
   }

   /// Attempts to initialize the cell with `value` without blocking.
   ///
   /// - If the cell is uninitialized and not locked, initializes it with `value` and returns `Ok(&value)`.
   /// - If the cell is already initialized, returns `Err(value)`.
   /// - If the cell is currently locked by another thread, returns `Err(value)`.
   #[inline]
   pub fn try_set(&self, value: T) -> Result<&T, T> {
      let Some(guard) = self.state.try_lock() else {
         return Err(value);
      };
      // SAFETY: We hold the lock, so we have exclusive access to initialize the value.
      let refv = unsafe { (*self.value.get()).write(value) };
      guard.commit();
      Ok(refv)
   }

   /// Replaces the cell's value, returning the old value if initialized.
   ///
   /// - If uninitialized, sets the value to `value` and returns `None`.
   /// - If initialized, replaces the existing value with `value` and returns the old value.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks.
   #[inline]
   pub fn replace_mut(&mut self, value: T) -> Option<T> {
      let mref = self.value.get_mut();

      if self.state.set_done() {
         // Was uninitialized, now set to done. Write the new value.
         mref.write(value);
         None
      } else {
         // Was already initialized. Replace the existing value.
         // SAFETY: We have exclusive access and the cell is initialized.
         let old_value = unsafe { mref.assume_init_mut() };
         Some(mem::replace(old_value, value))
      }
   }

   /// Gets a mutable reference, initializing with `value` if needed.
   ///
   /// - If initialized, returns a mutable reference to the existing value.
   /// - If uninitialized, initializes it with `value` and returns a mutable reference.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks.
   #[inline]
   pub fn get_mut_or_set(&mut self, value: T) -> &mut T {
      if self.state.set_done() {
         // Was uninitialized, now set to done. Write the new value.
         self.value.get_mut().write(value);
      }
      // SAFETY: The cell is guaranteed to be initialized here, either previously
      // or by the call above, and we have exclusive access.
      unsafe { self.get_unchecked_mut() }
   }

   /// Gets a mutable reference, initializing with `Default::default()` if needed.
   ///
   /// - If initialized, returns a mutable reference to the existing value.
   /// - If uninitialized, initializes it with `T::default()` and returns a mutable reference.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks.
   #[inline]
   pub fn get_mut_or_default(&mut self) -> &mut T
   where
      T: Default,
   {
      if self.state.set_done() {
         // Was uninitialized, now set to done. Write the default value.
         self.value.get_mut().write(T::default());
      }
      // SAFETY: The cell is guaranteed to be initialized here, either previously
      // or by the call above, and we have exclusive access.
      unsafe { self.get_unchecked_mut() }
   }

   /// Returns a reference to the value without checking if it's initialized.
   ///
   /// # Safety
   ///
   /// Calling this method on an uninitialized `Once` cell is *undefined behavior*.
   /// The caller must ensure the cell is initialized, e.g., by calling `is_done()` or `get()`.
   #[inline]
   pub unsafe fn get_unchecked(&self) -> &T {
      debug_assert!(self.is_done(), "get_unchecked called on uninitialized Once");
      // SAFETY: The caller guarantees that the cell is initialized.
      (*self.value.get()).assume_init_ref()
   }

   /// Returns a mutable reference to the value without checking if it's initialized.
   ///
   /// # Safety
   ///
   /// Calling this method on an uninitialized `Once` cell is *undefined behavior*.
   /// The caller must ensure the cell is initialized and that they have exclusive access.
   #[inline]
   pub unsafe fn get_unchecked_mut(&mut self) -> &mut T {
      debug_assert!(
         self.is_done(),
         "get_unchecked_mut called on uninitialized Once"
      );
      // SAFETY: The caller guarantees that the cell is initialized and we have exclusive access.
      unsafe { (*self.value.get()).assume_init_mut() }
   }

   /// Takes the value out of the cell, leaving it uninitialized.
   ///
   /// Returns `Some(value)` if the cell was initialized, `None` otherwise.
   /// Requires exclusive access (`&mut self`), so it never blocks.
   #[inline]
   pub fn take(&mut self) -> Option<T> {
      if self.state.set_uninit() {
         // Was initialized, now set to uninit. Read the value out.
         // SAFETY: The cell was initialized (guaranteed by set_uninit returning true).
         // The state is now uninitialized, preventing further reads of the old value.
         // We have exclusive access.
         unsafe { Some((*self.value.get()).assume_init_read()) }
      } else {
         // Was already uninitialized.
         None
      }
   }

   /// Initializes the cell with `value`. Blocks if another thread is initializing.
   ///
   /// - If uninitialized, initializes it with `value` and returns `Ok(())`.
   /// - If already initialized, returns `Err(value)`.
   ///
   /// Guarantees the cell is initialized upon return, but not necessarily with `value`
   /// if another thread completed initialization first.
   #[inline]
   pub fn set(&self, value: T) -> Result<(), T> {
      match self.try_insert(value) {
         Ok(_) => Ok(()), // Successfully inserted our value
         Err((_current_value, original_value)) => Err(original_value), // Already initialized by someone else
      }
   }

   /// Initializes the cell with `value` if uninitialized, returning a reference. Blocks if needed.
   ///
   /// - If uninitialized, initializes with `value` and returns `Ok(&value)`.
   /// - If already initialized, returns `Err((&current_value, value))`.
   ///
   /// Guarantees the cell is initialized upon return.
   #[inline]
   pub fn try_insert(&self, value: T) -> Result<&T, (&T, T)> {
      // `get_or_init` ensures initialization. We use `value` only if the cell was empty.
      let mut value_opt = Some(value);
      let res_ref = self.get_or_init(|| value_opt.take().unwrap());
      match value_opt {
         None => Ok(res_ref), // Our value was used for initialization
         Some(original_value) => Err((res_ref, original_value)), // Someone else initialized it first
      }
   }

   /// Gets the value, initializing with `f()` if needed. Blocks if needed.
   ///
   /// - If initialized, returns a reference to the existing value.
   /// - If uninitialized, calls `f()`, stores the result, and returns a reference.
   ///
   /// If multiple threads call this concurrently, only one `f()` execution happens.
   #[inline]
   pub fn get_or_init<F>(&self, f: F) -> &T
   where
      F: FnOnce() -> T,
   {
      if let Some(value) = self.get() {
         return value;
      }
      // Cold path: needs initialization
      self.initialize(f);
      // SAFETY: initialize ensures the value is now initialized.
      unsafe { self.get_unchecked() }
   }

   /// Gets a mutable reference, initializing with `f()` if needed.
   ///
   /// - If initialized, returns a mutable reference to the existing value.
   /// - If uninitialized, calls `f()`, stores the result, and returns a mutable reference.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks.
   #[inline]
   pub fn get_mut_or_init<F>(&mut self, f: F) -> &mut T
   where
      F: FnOnce() -> T,
   {
      if self.is_done() {
         // Already initialized.
      } else if let Some(guard) = self.state.try_lock() {
         // We got the lock (because is_done was false and no one else had it). Initialize it.
         // SAFETY: We hold the lock, exclusive access to initialize.
         unsafe { (*self.value.get()).write(f()) };
         guard.commit();
      } else {
         // This case should theoretically not happen with &mut self,
         // as try_lock should succeed if !is_done().
         // If it did, it implies a logic error or unexpected concurrent access.
         unreachable!("Could not lock for init despite having exclusive access");
      }

      // SAFETY: The cell is guaranteed to be initialized now, and we have exclusive access.
      unsafe { self.get_unchecked_mut() }
   }

   /// Gets the value, initializing with fallible `f()` if needed. Blocks if needed.
   ///
   /// - If initialized, returns `Ok(&value)`.
   /// - If uninitialized, calls `f()`:
   ///     - On `Ok(value)`, initializes the cell and returns `Ok(&value)`.
   ///     - On `Err(e)`, returns `Err(e)` and leaves the cell uninitialized.
   ///
   /// If multiple threads call this concurrently, only one `f()` execution happens.
   pub fn get_or_try_init<F, E>(&self, f: F) -> Result<&T, E>
   where
      F: FnOnce() -> Result<T, E>,
   {
      if let Some(value) = self.get() {
         return Ok(value);
      }
      // Cold path: needs initialization attempt
      self.try_initialize(f)?;
      // If try_initialize succeeded, it's now initialized.
      debug_assert!(self.is_done());
      // SAFETY: try_initialize succeeded, so the value is initialized.
      Ok(unsafe { self.get_unchecked() })
   }

   /// Gets a mutable reference, initializing with fallible `f()` if needed.
   ///
   /// - If initialized, returns `Ok(&mut value)`.
   /// - If uninitialized, calls `f()`:
   ///     - On `Ok(value)`, initializes the cell and returns `Ok(&mut value)`.
   ///     - On `Err(e)`, returns `Err(e)` and leaves the cell uninitialized.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks (initialization happens inline).
   pub fn get_mut_or_try_init<F, E>(&mut self, f: F) -> Result<&mut T, E>
   where
      F: FnOnce() -> Result<T, E>,
   {
      if let Some(guard) = self.state.try_lock() {
         // We got the lock. Try to initialize.
         self.value.get_mut().write(f()?);
         guard.commit();
      }
      // SAFETY: The cell is guaranteed to be initialized now (or we returned Err),
      // and we have exclusive access.
      Ok(unsafe { self.get_unchecked_mut() })
   }

   /// Gets the value, initializing asynchronously with `f()` if needed. Blocks if needed.
   ///
   /// - If initialized, returns a reference to the existing value.
   /// - If uninitialized, awaits `f()`, stores the result, and returns a reference.
   ///
   /// If multiple tasks call this concurrently, only one `f()` execution happens.
   #[inline]
   pub async fn get_or_init_async<F, Fut>(&self, f: F) -> &T
   where
      F: FnOnce() -> Fut,
      Fut: Future<Output = T>,
   {
      if let Some(value) = self.get() {
         return value;
      }
      // Cold path: needs async initialization
      self.initialize_async(f).await;
      // SAFETY: initialize_async ensures the value is now initialized.
      unsafe { self.get_unchecked() }
   }

   /// Gets a mutable reference, initializing asynchronously with `f()` if needed.
   ///
   /// - If initialized, returns a mutable reference to the existing value.
   /// - If uninitialized, awaits `f()`, stores the result, and returns a mutable reference.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks (initialization happens inline).
   #[inline]
   pub async fn get_mut_or_init_async<F, Fut>(&mut self, f: F) -> &mut T
   where
      F: FnOnce() -> Fut,
      Fut: Future<Output = T>,
   {
      if let Some(guard) = self.state.try_lock() {
         // We got the lock. Try to initialize.
         self.value.get_mut().write(f().await);
         guard.commit();
      }
      // SAFETY: The cell is guaranteed to be initialized now (or we returned Err),
      // and we have exclusive access.
      unsafe { self.get_unchecked_mut() }
   }

   /// Gets the value, initializing asynchronously with fallible `f()` if needed. Blocks if needed.
   ///
   /// - If initialized, returns `Ok(&value)`.
   /// - If uninitialized, awaits `f()`:
   ///     - On `Ok(value)`, initializes the cell and returns `Ok(&value)`.
   ///     - On `Err(e)`, returns `Err(e)` and leaves the cell uninitialized.
   ///
   /// If multiple tasks call this concurrently, only one `f()` execution happens.
   pub async fn get_or_try_init_async<F, Fut, E>(&self, f: F) -> Result<&T, E>
   where
      F: FnOnce() -> Fut,
      Fut: Future<Output = Result<T, E>>,
   {
      if let Some(value) = self.get() {
         return Ok(value);
      }
      // Cold path: needs async initialization attempt
      self.try_initialize_async(f).await?;
      // If try_initialize_async succeeded, it's now initialized.
      debug_assert!(self.is_done());
      // SAFETY: try_initialize_async succeeded, so the value is initialized.
      Ok(unsafe { self.get_unchecked() })
   }

   /// Gets a mutable reference, initializing asynchronously with fallible `f()` if needed.
   ///
   /// - If initialized, returns `Ok(&mut value)`.
   /// - If uninitialized, awaits `f()`:
   ///     - On `Ok(value)`, initializes the cell and returns `Ok(&mut value)`.
   ///     - On `Err(e)`, returns `Err(e)` and leaves the cell uninitialized.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks (initialization happens inline).
   pub async fn get_mut_or_try_init_async<F, Fut, E>(&mut self, f: F) -> Result<&mut T, E>
   where
      F: FnOnce() -> Fut,
      Fut: Future<Output = Result<T, E>>,
   {
      if let Some(guard) = self.state.try_lock() {
         // We got the lock. Try to initialize.
         self.value.get_mut().write(f().await?);
         guard.commit();
      }

      // SAFETY: The cell is guaranteed to be initialized now (or we returned Err),
      // and we have exclusive access.
      Ok(unsafe { self.get_unchecked_mut() })
   }

   // --- Internal Initialization Helpers ---

   /// Cold path for `get_or_init_async`. Acquires lock asynchronously and awaits initializer.
   #[cold]
   async fn initialize_async<F, Fut>(&self, f: F)
   where
      F: FnOnce() -> Fut,
      Fut: Future<Output = T>,
   {
      let Some(guard) = self.state.lock_async().await else {
         return; // Another task initialized it while we waited
      };
      // SAFETY: We hold the lock, exclusive access to initialize the value.
      unsafe { (*self.value.get()).write(f().await) };
      guard.commit(); // Mark as done and notify waiters
   }

   /// Cold path for `get_or_try_init_async`. Acquires lock asynchronously and awaits fallible initializer.
   #[cold]
   async fn try_initialize_async<Fn, Fut, E>(&self, f: Fn) -> Result<(), E>
   where
      Fn: FnOnce() -> Fut,
      Fut: Future<Output = Result<T, E>>,
   {
      let Some(guard) = self.state.lock_async().await else {
         return Ok(()); // Another task initialized it while we waited
      };
      let value = f().await?; // Await initializer. If it fails, guard is dropped, state reset.
                              // SAFETY: We hold the lock, exclusive access to initialize the value.
      unsafe { (*self.value.get()).write(value) };
      guard.commit(); // Mark as done and notify waiters
      Ok(())
   }

   /// Cold path for `get_or_init`. Acquires lock and calls initializer.
   #[cold]
   fn initialize<F>(&self, f: F)
   where
      F: FnOnce() -> T,
   {
      let Some(guard) = self.state.lock() else {
         return; // Another thread initialized it while we waited for the lock
      };
      // SAFETY: We hold the lock, exclusive access to initialize the value.
      unsafe { (*self.value.get()).write(f()) };
      guard.commit(); // Mark as done and notify waiters
   }

   /// Cold path for `get_or_try_init`. Acquires lock and calls fallible initializer.
   #[cold]
   fn try_initialize<F, E>(&self, f: F) -> Result<(), E>
   where
      F: FnOnce() -> Result<T, E>,
   {
      let Some(guard) = self.state.lock() else {
         return Ok(()); // Another thread initialized it while we waited for the lock
      };
      let value = f()?; // Call initializer. If it fails, guard is dropped, state reset.
                        // SAFETY: We hold the lock, exclusive access to initialize the value.
      unsafe { (*self.value.get()).write(value) };
      guard.commit(); // Mark as done and notify waiters
      Ok(())
   }
}

// --- Trait Implementations ---

impl<T> From<Option<T>> for Once<T> {
   /// Creates an initialized `Once` from `Some(value)` or an uninitialized one from `None`.
   fn from(value: Option<T>) -> Self {
      match value {
         Some(value) => Self::with_value(value),
         None => Self::new(),
      }
   }
}

// SAFETY:
// `&Once<T>` is `Sync` if `&T` is `Sync` (requiring `T: Sync`)
// and if the initialization mechanism is thread-safe (which it is).
// `T: Send` is also required because a value provided by one thread
// might be read or dropped by another.
unsafe impl<T: Sync + Send> Sync for Once<T> {}
// SAFETY:
// `Once<T>` is `Send` if `T` is `Send`, as the ownership of `T`
// can be transferred across threads via initialization or `take()`.
unsafe impl<T: Send> Send for Once<T> {}

impl<T> Default for Once<T> {
   /// Creates a new, uninitialized `Once` cell.
   #[inline]
   fn default() -> Once<T> {
      Once::new()
   }
}

impl<T: fmt::Display> fmt::Display for Once<T> {
   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      match self.get() {
         Some(v) => fmt::Display::fmt(v, f),
         None => f.write_str("<uninit>"),
      }
   }
}

impl<T: fmt::Debug> fmt::Debug for Once<T> {
   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      let mut d = f.debug_tuple("Once");
      match self.get() {
         Some(v) => d.field(v),
         None => d.field(&format_args!("<uninit>")),
      };
      d.finish()
   }
}

impl<T: Clone> Clone for Once<T> {
   /// Clones the `Once` cell.
   ///
   /// If the original cell is initialized, the clone will be initialized
   /// with a cloned value. If the original is uninitialized, the clone
   /// will also be uninitialized.
   #[inline]
   fn clone(&self) -> Once<T> {
      match self.get() {
         Some(value) => Self::with_value(value.clone()),
         None => Self::new(),
      }
   }
}

impl<T> From<T> for Once<T> {
   /// Creates a new, initialized `Once` cell from the given value.
   #[inline]
   fn from(value: T) -> Self {
      Self::with_value(value)
   }
}

impl<T: PartialEq> PartialEq for Once<T> {
   /// Checks if two `Once` cells are equal.
   ///
   /// They are equal if both are uninitialized, or if both are initialized
   /// and their contained values are equal according to `PartialEq`.
   #[inline]
   fn eq(&self, other: &Once<T>) -> bool {
      self.get() == other.get()
   }
}

impl<T: Eq> Eq for Once<T> {}

impl<T> Drop for Once<T> {
   #[inline]
   fn drop(&mut self) {
      if self.is_done() {
         // The state indicates the cell is initialized.
         // SAFETY: We have exclusive access (`&mut self`), the cell is initialized,
         // and we are dropping it, so the value won't be accessed again.
         unsafe { self.value.get_mut().assume_init_drop() };
      }
   }
}

// --- Internal State Management ---

/// Atomic state management for the `Once` cell.
struct OnceState(AtomicU32);

impl OnceState {
   /// Bit flag: Cell is initialized.
   const DONE: u32 = 1;
   /// Bit flag: Cell is locked for initialization.
   const LOCKED: u32 = 2;
   /// Bit flag: At least one thread is waiting for initialization.
   const WAITING: u32 = 4;
   /// Start of epoch bits (used to detect ABA issues, although primarily for waits).
   const EPOCH_1: u32 = 8;
   /// Mask for epoch bits.
   const EPOCH_MASK: u32 = !(Self::DONE | Self::LOCKED | Self::WAITING);

   /// Calculates the next epoch value based on the current state.
   #[inline(always)]
   fn next_epoch(current_state: u32) -> u32 {
      (current_state & Self::EPOCH_MASK).wrapping_add(Self::EPOCH_1) & Self::EPOCH_MASK
   }

   /// Creates a new state representing an uninitialized cell.
   #[inline]
   const fn new() -> Self {
      Self(AtomicU32::new(0)) // Initial state: 0 (no flags set)
   }

   /// Creates a new state representing an initialized cell.
   #[inline]
   const fn done() -> Self {
      Self(AtomicU32::new(Self::DONE)) // Initial state: DONE flag set
   }

   /// Notifies all waiting threads. Uses `parking_lot_core` futex wait/wake.
   #[inline]
   fn notify_all(&self) {
      // SAFETY: The address passed to unpark must match the address used for park.
      // We consistently use the address of the AtomicU32.
      unsafe {
         parking_lot_core::unpark_all(self.0.as_ptr() as usize, DEFAULT_UNPARK_TOKEN);
      }
   }

   /// Waits until the state changes from the provided `state` value.
   /// Uses `parking_lot_core` futex wait/wake.
   #[inline]
   fn wait(&self, expected_state: u32) {
      // SAFETY: See safety comment in `notify_all`.
      unsafe {
         // park() checks the condition closure *before* sleeping.
         // It only sleeps if the closure returns true (meaning state hasn't changed).
         let _ = parking_lot_core::park(
            self.0.as_ptr() as usize,
            || self.0.load(atomic::Ordering::Acquire) == expected_state, // Validate: still needs waiting?
            || {},                                                       // Before sleep callback
            |_, _| {},          // Timed out callback (we don't use timeouts)
            DEFAULT_PARK_TOKEN, // Token passed to unpark
            None,               // No timeout
         );
         // We ignore the park result; wake-up could be spurious or due to state change.
         // The outer loops will re-check the state.
      }
   }

   /// Sets the state to DONE, increments epoch, and notifies waiters based on the *previous* state.
   /// Returns `true` if the state was *not* previously DONE.
   ///
   /// This is safe to call when holding the lock (`OnceGuard`) or `&mut self`.
   #[inline]
   fn set_done(&self) -> bool {
      // Read the current state to calculate the next epoch *before* the swap.
      // Relaxed ordering is sufficient because the subsequent swap has Release ordering.
      let current_state = self.0.load(Ordering::Relaxed);
      let next_epoch = Self::next_epoch(current_state);
      let new_state = Self::DONE | next_epoch;

      // Atomically swap the new state in and get the previous state.
      // Release ordering ensures that the write to the Once<T>'s value happens-before
      // this state change is observed by other threads (via Acquire loads).
      let prev_state = self.0.swap(new_state, Ordering::Release);

      // Notify waiters if the WAITING flag was set in the *previous* state.
      if prev_state & Self::WAITING != 0 {
         self.notify_all();
      }

      // Return true if the DONE flag was *not* set in the previous state.
      prev_state & Self::DONE == 0
   }

   /// Sets the state to uninitialized (clears DONE/LOCKED), increments epoch,
   /// and notifies waiters based on the *previous* state.
   /// Returns `true` if the state was previously DONE.
   ///
   /// This is safe to call when holding the lock (`OnceGuard`) or `&mut self`.
   #[inline]
   fn set_uninit(&self) -> bool {
      // Read the current state to calculate the next epoch *before* the swap.
      let current_state = self.0.load(Ordering::Relaxed);
      let next_epoch = Self::next_epoch(current_state);
      // New state is just the new epoch, implicitly clearing DONE, LOCKED, WAITING.
      let new_state = next_epoch;

      // Atomically swap the new state in and get the previous state.
      // Release ordering ensures that any prior operations (like reading the value
      // in `take`) happen-before this state change is observed. It also ensures
      // that if initialization failed (Guard::drop), the state reset happens-before
      // another thread might try to lock again.
      let prev_state = self.0.swap(new_state, Ordering::Release);

      // Notify waiters if the WAITING flag was set in the *previous* state.
      // This handles waking threads if initialization failed within the guard.
      if prev_state & Self::WAITING != 0 {
         self.notify_all();
      }

      // Return true if the DONE flag *was* set in the previous state.
      prev_state & Self::DONE != 0
   }

   /// Checks if the DONE flag is set.
   #[inline]
   fn is_done(&self, ordering: Ordering) -> bool {
      self.0.load(ordering) & Self::DONE != 0
   }

   /// Tries to acquire the initialization lock. Internal helper for `lock`, `try_lock`, `lock_async`.
   ///
   /// Args:
   ///   - `nowait`: If true, don't set the WAITING flag if the lock is held.
   ///
   /// Returns:
   ///   - `Ok(None)`: Cell is already initialized (DONE flag is set).
   ///   - `Ok(Some(guard))`: Lock acquired successfully.
   ///   - `Err(current_state)`: Lock is currently held by another thread. `current_state` includes WAITING if set.
   #[inline]
   fn lock_step(&self, nowait: bool) -> Result<Option<OnceGuard<'_>>, u32> {
      loop {
         let current_state = self.0.load(Ordering::Relaxed);
         // Fast path: Already initialized?
         if current_state & Self::DONE != 0 {
            return Ok(None);
         }

         // Try to acquire the lock if it's not held.
         if current_state & Self::LOCKED == 0 {
            // Attempt to set the LOCKED flag. Epoch doesn't change here.
            let new_state = current_state | Self::LOCKED;
            match self.0.compare_exchange_weak(
               current_state,
               new_state,
               Ordering::Acquire, // Ensure visibility of state *before* lock acquisition
               Ordering::Relaxed,
            ) {
               Ok(_) => return Ok(Some(OnceGuard::new(self))), // Lock acquired!
               Err(_) => {
                  std::hint::spin_loop();
                  continue;
               }
            }
         } else {
            // Lock is held by someone else.
            // If we need to wait and the WAITING flag isn't set yet, try setting it.
            if !nowait && (current_state & Self::WAITING == 0) {
               let new_state = current_state | Self::WAITING;
               match self.0.compare_exchange_weak(
                  current_state,
                  new_state,
                  Ordering::Relaxed, // Setting WAITING doesn't need strong ordering itself
                  Ordering::Relaxed,
               ) {
                  Ok(_) => {
                     // Successfully set WAITING flag. Return Err with the *new* state.
                     return Err(new_state);
                  }
                  Err(_) => {
                     // CAS failed, retry the outer loop. The state might have changed (e.g., became DONE).
                     std::hint::spin_loop();
                     continue;
                  }
               }
            } else {
               // Lock is held, and either we shouldn't wait (`nowait`) or WAITING is already set.
               // Return Err with the current state we observed.
               return Err(current_state);
            }
         }
      }
   }

   /// Acquires the initialization lock, blocking if necessary.
   ///
   /// Returns `Some(guard)` if the lock was acquired (cell was not initialized).
   /// Returns `None` if the cell was already initialized.
   #[inline]
   fn lock(&self) -> Option<OnceGuard<'_>> {
      match self.lock_step(false) {
         Ok(guard_opt) => guard_opt, // Either got lock or was already done
         Err(mut state_when_failed) => {
            // Lock was held, need to wait. Loop until lock_step succeeds or indicates done.
            loop {
               // Wait only if the state hasn't changed from what lock_step observed.
               self.wait(state_when_failed);
               // After waking up, try locking again.
               match self.lock_step(false) {
                  Ok(guard_opt) => return guard_opt,
                  Err(new_state) => {
                     // Still locked, update the state we wait for and loop.
                     state_when_failed = new_state;
                  }
               }
            }
         }
      }
   }

   /// Acquires the initialization lock asynchronously.
   ///
   /// Tries spinning/yielding first, then falls back to `block_in_place`.
   #[inline]
   async fn lock_async(&self) -> Option<OnceGuard<'_>> {
      loop {
         // Spin/yield loop
         for _ in 0..16 {
            // Outer loop limit
            match self.lock_step(false) {
               Ok(guard_opt) => return guard_opt,
               Err(state) => {
                  // Yield to allow other tasks to run, hoping the lock holder finishes.
                  for _ in 0..32 {
                     // Inner yield loop
                     #[cfg(any(feature = "async-tokio", feature = "async-tokio-mt"))]
                     tokio::task::yield_now().await;
                     // Check if state changed *after* yielding, maybe it's free now?
                     if self.0.load(Ordering::Relaxed) != state {
                        break; // State changed, retry lock_step in outer loop
                     }
                  }
                  // If inner loop finished without state change, continue outer loop.
               }
            }
         }

         // Fallback to blocking wait if spin/yield didn't work
         #[cfg(feature = "async-tokio-mt")]
         {
            return match self.lock_step(false) {
               Ok(x) => x,
               Err(state) => tokio::task::block_in_place(|| {
                  self.wait(state);
                  self.lock()
               }),
            };
         }
      }
   }

   /// Attempts to acquire the lock without blocking.
   ///
   /// Returns `Some(guard)` if the lock was acquired immediately.
   /// Returns `None` if the cell was already initialized OR if the lock was held by another thread.
   #[inline]
   fn try_lock(&self) -> Option<OnceGuard<'_>> {
      // Use lock_step with nowait = true.
      // If it returns Err, it means locked by someone else -> return None.
      // If it returns Ok(None), it means already done -> return None.
      // If it returns Ok(Some(guard)), return Some(guard).
      self.lock_step(true).ok().flatten()
   }
}

/// RAII guard returned by `lock`, `try_lock`, etc.
/// Manages the `LOCKED` state. If dropped, resets state to uninitialized.
/// Must be `commit()`ed to mark the cell as initialized (`DONE`).
struct OnceGuard<'a> {
   state: &'a OnceState,
}

impl<'a> OnceGuard<'a> {
   /// Creates a new guard. Assumes the `LOCKED` flag is already set on `state`.
   #[inline]
   const fn new(state: &'a OnceState) -> Self {
      Self { state }
   }

   /// Marks initialization as complete (`DONE`), consumes the guard, and notifies waiters.
   /// Returns `true` if the state was successfully changed from !DONE to DONE.
   #[inline]
   fn commit(self) -> bool {
      let success = self.state.set_done();
      mem::forget(self); // Prevent Drop from running (which would reset state)
      success
   }
}

impl<'a> Drop for OnceGuard<'a> {
   /// Called if initialization is cancelled (e.g., due to panic or error in `try_init`).
   /// Resets the state to uninitialized (clears `LOCKED`), allowing another thread to try.
   fn drop(&mut self) {
      self.state.set_uninit(); // Resets state and notifies waiters
   }
}

#[cfg(test)]
mod tests {
   use std::sync::atomic::{AtomicUsize, Ordering};
   use std::sync::Arc;
   use std::thread;
   use std::time::Duration;

   use super::*;

   #[test]
   fn test_new_is_not_done() {
      let once: Once<i32> = Once::new();
      assert!(!once.is_done());
      assert_eq!(once.get(), None);
   }

   #[test]
   fn test_with_value_is_done() {
      let once = Once::with_value(42);
      assert!(once.is_done());
      assert_eq!(once.get(), Some(&42));
   }

   #[test]
   fn test_get_or_init() {
      let once: Once<i32> = Once::new();
      let counter = AtomicUsize::new(0);
      let value = once.get_or_init(|| {
         counter.fetch_add(1, Ordering::SeqCst);
         42
      });
      assert_eq!(value, &42);
      assert!(once.is_done());
      assert_eq!(counter.load(Ordering::SeqCst), 1);

      // Second call should not execute the closure
      let value = once.get_or_init(|| {
         counter.fetch_add(1, Ordering::SeqCst);
         panic!("Should not be called")
      });
      assert_eq!(value, &42);
      assert_eq!(counter.load(Ordering::SeqCst), 1); // Counter didn't increase
   }

   #[test]
   fn test_try_set_recursive() {
      // Test scenario where `try_set` is called from within `get_or_init`'s closure.
      // This shouldn't deadlock, but `try_set` should fail as the lock is held.
      let once: Once<i32> = Once::new();
      once.get_or_init(|| {
         // We are inside the initialization closure, the lock is held.
         // try_set should fail because the lock is already held (by us).
         let x = once.try_set(44);
         assert!(
            matches!(x, Err(44)),
            "Expected try_set to fail while locked"
         );
         42 // The actual initialization value
      });
      assert!(once.is_done());
      assert_eq!(once.get(), Some(&42));
   }

   #[test]
   fn test_try_set() {
      let once: Once<i32> = Once::new();

      // First try_set should succeed
      assert_eq!(once.try_set(42), Ok(&42));
      assert!(once.is_done());
      assert_eq!(once.get(), Some(&42));

      // Second try_set should fail because it's already initialized
      assert_eq!(once.try_set(24), Err(24));
      assert_eq!(once.get(), Some(&42)); // Value remains unchanged
   }

   #[test]
   fn test_set() {
      let once: Once<i32> = Once::new();

      // First set should succeed
      assert_eq!(once.set(42), Ok(()));
      assert!(once.is_done());
      assert_eq!(once.get(), Some(&42));

      // Second set should fail
      assert_eq!(once.set(24), Err(24));
      assert_eq!(once.get(), Some(&42)); // Value remains unchanged
   }

   #[test]
   fn test_get_or_try_init() {
      let once_ok: Once<i32> = Once::new();
      let counter_ok = AtomicUsize::new(0);

      // Should initialize with Ok value
      let result = once_ok.get_or_try_init(|| {
         counter_ok.fetch_add(1, Ordering::SeqCst);
         Ok::<_, &str>(42)
      });
      assert_eq!(result, Ok(&42));
      assert!(once_ok.is_done());
      assert_eq!(counter_ok.load(Ordering::SeqCst), 1);

      // Second call should return existing value, not run closure
      let result = once_ok.get_or_try_init(|| {
         counter_ok.fetch_add(1, Ordering::SeqCst);
         Ok::<_, &str>(99) // Different value to check it's not used
      });
      assert_eq!(result, Ok(&42));
      assert_eq!(counter_ok.load(Ordering::SeqCst), 1); // Counter didn't increase

      // Test initialization failure
      let once_err: Once<i32> = Once::new();
      let counter_err = AtomicUsize::new(0);
      let result = once_err.get_or_try_init(|| {
         counter_err.fetch_add(1, Ordering::SeqCst);
         Err::<i32, _>("init error")
      });
      assert_eq!(result, Err("init error"));
      assert!(!once_err.is_done()); // Should remain uninitialized
      assert_eq!(counter_err.load(Ordering::SeqCst), 1);

      // Try initializing again after failure, this time successfully
      let result = once_err.get_or_try_init(|| {
         counter_err.fetch_add(1, Ordering::SeqCst);
         Ok::<_, &str>(55)
      });
      assert_eq!(result, Ok(&55));
      assert!(once_err.is_done());
      assert_eq!(counter_err.load(Ordering::SeqCst), 2); // Counter increased again
   }

   #[test]
   fn test_take() {
      let mut once = Once::with_value(42);
      assert!(once.is_done());
      assert_eq!(once.take(), Some(42));
      assert!(!once.is_done());
      assert_eq!(once.get(), None);
      assert_eq!(once.take(), None); // Taking again yields None

      // Taking from initially empty cell
      let mut empty: Once<i32> = Once::new();
      assert!(!empty.is_done());
      assert_eq!(empty.take(), None);
      assert!(!empty.is_done());
   }

   #[test]
   fn test_multi_thread_get_or_init() {
      let once = Arc::new(Once::new());
      let init_counter = Arc::new(AtomicUsize::new(0));
      let threads: Vec<_> = (0..10)
         .map(|_| {
            let once_clone = Arc::clone(&once);
            let counter_clone = Arc::clone(&init_counter);
            thread::spawn(move || {
               // Simulate some delay/contention
               thread::sleep(Duration::from_millis(10));
               *once_clone.get_or_init(|| {
                  counter_clone.fetch_add(1, Ordering::SeqCst);
                  // More delay during initialization
                  thread::sleep(Duration::from_millis(20));
                  42
               })
            })
         })
         .collect();

      // All threads should get the same value
      for handle in threads {
         assert_eq!(handle.join().unwrap(), 42);
      }
      assert_eq!(once.get(), Some(&42));
      // Crucially, the initializer should only have run once
      assert_eq!(init_counter.load(Ordering::SeqCst), 1);
   }

   #[test]
   fn test_multi_thread_set_race() {
      let once = Arc::new(Once::new());
      let successes = Arc::new(AtomicUsize::new(0));
      let threads: Vec<_> = (0..10)
         .map(|i| {
            let once_clone = Arc::clone(&once);
            let successes_clone = Arc::clone(&successes);
            thread::spawn(move || {
               thread::sleep(Duration::from_millis(5)); // Introduce slight offset
               match once_clone.set(i) {
                  Ok(()) => {
                     successes_clone.fetch_add(1, Ordering::SeqCst);
                     i // Return the value this thread *successfully* set
                  }
                  Err(_) => {
                     // Failed to set, get the value set by the winner
                     *once_clone
                        .get()
                        .expect("Cell must be initialized after set race")
                  }
               }
            })
         })
         .collect();

      let mut first_val = None;
      for handle in threads {
         let val = handle.join().unwrap();
         if first_val.is_none() {
            first_val = Some(val); // Capture the value set by the winning thread
         }
         // All threads should observe the same final value
         assert_eq!(Some(val), first_val);
      }
      // Exactly one thread should succeed in setting the value
      assert_eq!(successes.load(Ordering::SeqCst), 1);
      // The final value should be the one set by the winning thread
      assert_eq!(once.get().copied(), first_val);
   }

   #[test]
   fn test_from_option() {
      let once_some: Once<i32> = Once::from(Some(42));
      assert!(once_some.is_done());
      assert_eq!(once_some.get(), Some(&42));

      let once_none: Once<i32> = Once::from(None);
      assert!(!once_none.is_done());
      assert_eq!(once_none.get(), None);
   }

   // --- Tests specifically added to cover dead_code warnings ---

   #[test]
   fn test_replace_mut() {
      // Replace in initialized cell
      let mut once = Once::with_value(42);
      assert_eq!(once.get(), Some(&42));
      assert_eq!(once.replace_mut(84), Some(42));
      assert_eq!(once.get(), Some(&84));
      assert!(once.is_done());

      // Replace in uninitialized cell
      let mut empty: Once<i32> = Once::new();
      assert_eq!(empty.get(), None);
      assert_eq!(empty.replace_mut(42), None);
      assert_eq!(empty.get(), Some(&42));
      assert!(empty.is_done());
   }

   #[test]
   fn test_get_mut_or_set() {
      let mut once: Once<String> = Once::new();

      // First call initializes
      {
         let value = once.get_mut_or_set(String::from("hello"));
         assert_eq!(value, "hello");
         value.push_str(" world");
      }
      assert_eq!(once.get(), Some(&String::from("hello world")));
      assert!(once.is_done());

      // Second call gets existing value
      {
         let value = once.get_mut_or_set(String::from("discarded")); // This value is ignored
         assert_eq!(value, "hello world");
         value.push_str("!");
      }
      assert_eq!(once.get(), Some(&String::from("hello world!")));
      assert!(once.is_done());
   }

   #[test]
   fn test_get_mut_or_default() {
      let mut once: Once<Vec<i32>> = Once::new(); // Vec::default() is empty vec

      // First call initializes with default
      {
         let value = once.get_mut_or_default();
         assert!(value.is_empty());
         value.push(1);
      }
      assert_eq!(once.get(), Some(&vec![1]));
      assert!(once.is_done());

      // Second call gets existing value
      {
         let value = once.get_mut_or_default(); // Default is ignored
         assert_eq!(value, &vec![1]);
         value.push(2);
      }
      assert_eq!(once.get(), Some(&vec![1, 2]));
      assert!(once.is_done());
   }

   #[test]
   fn test_try_insert() {
      let once: Once<i32> = Once::new();

      // First insert should succeed and use the value
      let result = once.try_insert(42);
      assert!(matches!(result, Ok(&42)), "First insert failed");
      assert_eq!(once.get(), Some(&42));
      assert!(once.is_done());

      // Second insert should fail and return both current and rejected values
      let result = once.try_insert(84);
      match result {
         Err((current_ref, rejected_val)) => {
            assert_eq!(*current_ref, 42);
            assert_eq!(rejected_val, 84);
         }
         Ok(_) => panic!("Second insert should have failed"),
      }
      assert_eq!(once.get(), Some(&42)); // Value remains unchanged

      // Test try_insert calls get_or_init internally, check init function call count
      let once2: Once<i32> = Once::new();
      let _ = once2.try_insert(100); // Runs initializer
      let _ = once2.try_insert(200); // Does not run initializer

      // To properly test initializer count, need get_or_init test structure
      let once3: Once<i32> = Once::new();
      let counter3 = AtomicUsize::new(0);
      let f = || {
         counter3.fetch_add(1, Ordering::SeqCst);
         111
      };
      let mut val_opt = Some(f());
      let _ = once3.get_or_init(|| val_opt.take().unwrap()); // Simulates try_insert's internal call
      assert_eq!(counter3.load(Ordering::SeqCst), 1);

      let mut val2_opt = Some(222); // New value for second "simulated" try_insert
      let _ = once3.get_or_init(|| val2_opt.take().unwrap()); // This won't run closure
      assert_eq!(counter3.load(Ordering::SeqCst), 1); // Counter still 1
      assert!(val2_opt.is_some()); // Closure wasn't called, value wasn't taken
   }

   #[test]
   fn test_get_mut_or_init() {
      let mut once: Once<String> = Once::new();
      let counter = AtomicUsize::new(0);

      // First call initializes
      {
         let value = once.get_mut_or_init(|| {
            counter.fetch_add(1, Ordering::SeqCst);
            String::from("init")
         });
         assert_eq!(value, "init");
         assert_eq!(counter.load(Ordering::SeqCst), 1);
         value.push_str("ial");
      }
      assert_eq!(once.get(), Some(&String::from("initial")));
      assert!(once.is_done());

      // Second call gets existing value, closure not called
      {
         let value = once.get_mut_or_init(|| {
            counter.fetch_add(1, Ordering::SeqCst);
            panic!("Should not be called");
         });
         assert_eq!(value, "initial");
         assert_eq!(counter.load(Ordering::SeqCst), 1); // Counter unchanged
         value.push_str("ized");
      }
      assert_eq!(once.get(), Some(&String::from("initialized")));
      assert!(once.is_done());
   }

   #[test]
   fn test_get_mut_or_try_init() {
      let mut once_ok: Once<String> = Once::new();
      let counter_ok = AtomicUsize::new(0);

      // First call initializes successfully
      {
         let result = once_ok.get_mut_or_try_init(|| {
            counter_ok.fetch_add(1, Ordering::SeqCst);
            Ok::<_, &str>(String::from("ok"))
         });
         assert!(result.is_ok());
         let value = result.unwrap();
         assert_eq!(value, "ok");
         assert_eq!(counter_ok.load(Ordering::SeqCst), 1);
         value.push_str("ay");
      }
      assert_eq!(once_ok.get(), Some(&String::from("okay")));
      assert!(once_ok.is_done());

      // Second call gets existing value, closure not called
      {
         let result = once_ok.get_mut_or_try_init(|| {
            counter_ok.fetch_add(1, Ordering::SeqCst);
            Ok::<_, &str>(String::from("ignored"))
         });
         assert!(result.is_ok());
         let value = result.unwrap();
         assert_eq!(value, "okay");
         assert_eq!(counter_ok.load(Ordering::SeqCst), 1); // Counter unchanged
         value.push_str("!");
      }
      assert_eq!(once_ok.get(), Some(&String::from("okay!")));

      // Test initialization failure
      let mut once_err: Once<String> = Once::new();
      let counter_err = AtomicUsize::new(0);
      let result = once_err.get_mut_or_try_init(|| {
         counter_err.fetch_add(1, Ordering::SeqCst);
         Err::<String, _>("fail")
      });
      assert_eq!(result, Err("fail"));
      assert!(!once_err.is_done()); // Remains uninitialized
      assert_eq!(counter_err.load(Ordering::SeqCst), 1);
      assert_eq!(once_err.get(), None);

      // Try again successfully
      {
         let result = once_err.get_mut_or_try_init(|| {
            counter_err.fetch_add(1, Ordering::SeqCst);
            Ok::<_, &str>(String::from("retry ok"))
         });
         assert!(result.is_ok());
         let value = result.unwrap();
         assert_eq!(value, "retry ok");
         assert_eq!(counter_err.load(Ordering::SeqCst), 2); // Counter increased
      }
      assert!(once_err.is_done());
      assert_eq!(once_err.get(), Some(&String::from("retry ok")));
   }

   #[tokio::test]
   async fn test_get_or_init_async() {
      let once: Once<i32> = Once::new();
      let counter = Arc::new(AtomicUsize::new(0));

      let value = once
         .get_or_init_async(|| {
            let counter_clone = Arc::clone(&counter);
            async move {
               counter_clone.fetch_add(1, Ordering::SeqCst);
               tokio::time::sleep(Duration::from_millis(10)).await;
               42
            }
         })
         .await;

      assert_eq!(value, &42);
      assert!(once.is_done());
      assert_eq!(counter.load(Ordering::SeqCst), 1);

      // Second call should not execute the future
      let value = once
         .get_or_init_async(|| async {
            counter.fetch_add(1, Ordering::SeqCst); // This shouldn't run
            panic!("Should not be called");
         })
         .await;

      assert_eq!(value, &42);
      assert_eq!(counter.load(Ordering::SeqCst), 1); // Counter unchanged
   }

   #[tokio::test]
   async fn test_get_mut_or_init_async() {
      let mut once: Once<String> = Once::new();
      let counter = AtomicUsize::new(0);

      // First call initializes
      {
         let value = once
            .get_mut_or_init_async(|| {
               let current_count = counter.fetch_add(1, Ordering::SeqCst);
               async move {
                  tokio::time::sleep(Duration::from_millis(5)).await;
                  format!("init {}", current_count)
               }
            })
            .await;
         assert_eq!(value, "init 0");
         assert_eq!(counter.load(Ordering::SeqCst), 1);
         value.push_str("ial");
      }
      assert_eq!(once.get(), Some(&String::from("init 0ial")));
      assert!(once.is_done());

      // Second call gets existing value, future not created/polled
      {
         let value = once
            .get_mut_or_init_async(|| async {
               counter.fetch_add(1, Ordering::SeqCst); // Should not run
               panic!("Should not be called");
            })
            .await;
         assert_eq!(value, "init 0ial");
         assert_eq!(counter.load(Ordering::SeqCst), 1); // Counter unchanged
         value.push_str("ized");
      }
      assert_eq!(once.get(), Some(&String::from("init 0ialized")));
      assert!(once.is_done());
   }

   #[tokio::test]
   async fn test_get_or_try_init_async() {
      let once_ok: Once<String> = Once::new();
      let counter_ok = Arc::new(AtomicUsize::new(0));

      // First call initializes successfully
      let result = once_ok
         .get_or_try_init_async(|| {
            let counter_clone = Arc::clone(&counter_ok);
            async move {
               counter_clone.fetch_add(1, Ordering::SeqCst);
               tokio::time::sleep(Duration::from_millis(5)).await;
               Ok::<_, &str>(String::from("async ok"))
            }
         })
         .await;

      assert!(result.is_ok());
      assert_eq!(result.unwrap(), "async ok");
      assert!(once_ok.is_done());
      assert_eq!(counter_ok.load(Ordering::SeqCst), 1);

      // Second call gets existing value
      let result = once_ok
         .get_or_try_init_async(|| async {
            counter_ok.fetch_add(1, Ordering::SeqCst); // Should not run
            Ok::<_, &str>(String::from("ignored"))
         })
         .await;
      assert!(result.is_ok());
      assert_eq!(result.unwrap(), "async ok");
      assert_eq!(counter_ok.load(Ordering::SeqCst), 1); // Counter unchanged

      // Test initialization failure
      let once_err: Once<String> = Once::new();
      let counter_err = Arc::new(AtomicUsize::new(0));
      let result = once_err
         .get_or_try_init_async(|| {
            let counter_clone = Arc::clone(&counter_err);
            async move {
               counter_clone.fetch_add(1, Ordering::SeqCst);
               tokio::time::sleep(Duration::from_millis(5)).await;
               Err::<String, _>("async fail")
            }
         })
         .await;
      assert_eq!(result, Err("async fail"));
      assert!(!once_err.is_done()); // Remains uninitialized
      assert_eq!(counter_err.load(Ordering::SeqCst), 1);
      assert_eq!(once_err.get(), None);

      // Try again successfully
      let result = once_err
         .get_or_try_init_async(|| {
            let counter_clone = Arc::clone(&counter_err);
            async move {
               counter_clone.fetch_add(1, Ordering::SeqCst);
               tokio::time::sleep(Duration::from_millis(5)).await;
               Ok::<_, &str>(String::from("async retry ok"))
            }
         })
         .await;
      assert!(result.is_ok());
      assert_eq!(result.unwrap(), "async retry ok");
      assert!(once_err.is_done());
      assert_eq!(counter_err.load(Ordering::SeqCst), 2); // Counter increased
   }

   #[tokio::test]
   async fn test_get_mut_or_try_init_async() {
      let mut once_ok: Once<String> = Once::new();
      let counter_ok = AtomicUsize::new(0);

      // First call initializes successfully
      {
         let result = once_ok
            .get_mut_or_try_init_async(|| {
               let current_count = counter_ok.fetch_add(1, Ordering::SeqCst);
               async move {
                  tokio::time::sleep(Duration::from_millis(5)).await;
                  Ok::<_, &str>(format!("mut async ok {}", current_count))
               }
            })
            .await;
         assert!(result.is_ok());
         let value = result.unwrap();
         assert_eq!(value, "mut async ok 0");
         assert_eq!(counter_ok.load(Ordering::SeqCst), 1);
         value.push_str("!");
      }
      assert_eq!(once_ok.get(), Some(&String::from("mut async ok 0!")));
      assert!(once_ok.is_done());

      // Second call gets existing value
      {
         let result = once_ok
            .get_mut_or_try_init_async(|| async {
               counter_ok.fetch_add(1, Ordering::SeqCst); // Should not run
               Ok::<_, &str>(String::from("ignored"))
            })
            .await;
         assert!(result.is_ok());
         let value = result.unwrap();
         assert_eq!(value, "mut async ok 0!");
         assert_eq!(counter_ok.load(Ordering::SeqCst), 1); // Counter unchanged
      }

      // Test initialization failure
      let mut once_err: Once<String> = Once::new();
      let counter_err = AtomicUsize::new(0);
      let result = once_err
         .get_mut_or_try_init_async(|| {
            let current_count = counter_err.fetch_add(1, Ordering::SeqCst);
            async move {
               tokio::time::sleep(Duration::from_millis(5)).await;
               Err::<String, _>(format!("mut async fail {}", current_count))
            }
         })
         .await;
      assert_eq!(result, Err(String::from("mut async fail 0")));
      assert!(!once_err.is_done()); // Remains uninitialized
      assert_eq!(counter_err.load(Ordering::SeqCst), 1);
      assert_eq!(once_err.get(), None);

      // Try again successfully
      {
         let result = once_err
            .get_mut_or_try_init_async(|| {
               let current_count = counter_err.fetch_add(1, Ordering::SeqCst);
               async move {
                  tokio::time::sleep(Duration::from_millis(5)).await;
                  Ok::<_, String>(format!("mut async retry ok {}", current_count))
               }
            })
            .await;
         assert!(result.is_ok());
         let value = result.unwrap();
         assert_eq!(value, "mut async retry ok 1");
         assert_eq!(counter_err.load(Ordering::SeqCst), 2); // Counter increased
      }
      assert!(once_err.is_done());
      assert!(once_err.get().unwrap().starts_with("mut async retry ok 1"));
   }

   #[test]
   fn test_clone() {
      let once = Once::with_value(42);
      let clone = once.clone();

      assert_eq!(once.get(), Some(&42));
      assert_eq!(clone.get(), Some(&42));
      assert!(once.is_done());
      assert!(clone.is_done());

      let empty: Once<i32> = Once::new();
      let empty_clone = empty.clone();

      assert_eq!(empty.get(), None);
      assert_eq!(empty_clone.get(), None);
      assert!(!empty.is_done());
      assert!(!empty_clone.is_done());

      // Ensure clone state is independent
      let empty_clone_mut = empty_clone;
      empty_clone_mut.set(99).unwrap();
      assert_eq!(empty.get(), None);
      assert_eq!(empty_clone_mut.get(), Some(&99));
   }
}
