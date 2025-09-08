//! Standard once cell for one-time initialization.
//!
//! This module provides the [`Once<T>`] type, a thread-safe cell that can be
//! written to exactly once. It's useful for lazy initialization of global state,
//! caching expensive computations, or any scenario where you need to ensure
//! initialization happens exactly once across multiple threads.
//!
//! The implementation uses atomic operations for the fast path (checking if
//! initialized) and futex-based synchronization for the slow path (waiting
//! for initialization to complete).

use core::cell::UnsafeCell;
use core::future::Future;
use core::sync::atomic::Ordering;
use core::{fmt, mem};

use super::state::OnceLock;

/// A thread-safe cell which can be written to only once.
///
/// This structure provides safe initialization for values that might be accessed
/// concurrently by multiple threads. It ensures that the initialization logic
/// runs only once, even if multiple threads attempt to initialize the value simultaneously.
///
/// It uses atomic operations and `parking_lot`'s futex-based synchronization for
/// efficient blocking when necessary.
pub struct Once<T> {
   value: UnsafeCell<mem::MaybeUninit<T>>,
   lock: OnceLock,
}

impl<T> Once<T> {
   /// Creates a new, uninitialized `Once` cell.
   #[inline]
   #[must_use]
   pub const fn new() -> Self {
      Self {
         lock: OnceLock::new(),
         value: UnsafeCell::new(mem::MaybeUninit::uninit()),
      }
   }

   /// Creates a new `Once` cell that is already initialized with the given value.
   #[inline]
   #[must_use]
   pub const fn with_value(value: T) -> Self {
      Self {
         lock: OnceLock::done(),
         value: UnsafeCell::new(mem::MaybeUninit::new(value)),
      }
   }

   /// Checks if the cell has been initialized.
   ///
   /// This method never blocks.
   #[inline]
   pub fn is_done(&self) -> bool {
      self.lock.is_done(Ordering::Relaxed)
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
      let Some(guard) = self.lock.try_lock() else {
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

      if self.lock.set_done() {
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
      if self.lock.set_done() {
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
      if self.lock.set_done() {
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
      if self.lock.set_uninit() {
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
      } else if let Some(guard) = self.lock.try_lock() {
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
      if let Some(guard) = self.lock.try_lock() {
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
      if let Some(guard) = self.lock.try_lock() {
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
      if let Some(guard) = self.lock.try_lock() {
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
      let Some(guard) = self.lock.lock_async().await else {
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
      let Some(guard) = self.lock.lock_async().await else {
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
      let Some(guard) = self.lock.lock() else {
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
      let Some(guard) = self.lock.lock() else {
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
   fn default() -> Self {
      Self::new()
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
   fn clone(&self) -> Self {
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
   fn eq(&self, other: &Self) -> bool {
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
