//! Parameterized once cell with transformation support.
//!
//! This module provides the [`TOnce<P, T>`] type, a thread-safe cell that stores
//! a parameter of type `P` and transforms it into a value of type `T` on first access.
//! This is useful when you need to defer expensive initialization that requires
//! input data, or when the initialization parameters are known at construction
//! but the computation should be lazy.
//!
//! The key difference from `Once<T>` is that `TOnce<P, T>` stores the parameter
//! until initialization, then replaces it with the computed value. This allows
//! for more flexible initialization patterns where the initialization logic
//! needs access to stored state.
//!
//! Like `Once`, it uses atomic operations for the fast path and futex-based
//! synchronization for the slow path.

use core::cell::UnsafeCell;
use core::future::Future;
use core::sync::atomic::Ordering;
use core::{fmt, mem};

use super::state::OnceLock;
use crate::state::OnceGuard;

/// Internal enum to hold either the parameter or the initialized value.
union TOnceState<P, T> {
   pending: mem::ManuallyDrop<P>,
   init: mem::ManuallyDrop<T>,
}

impl<P, T> TOnceState<P, T> {
   #[inline(always)]
   const fn pending(value: P) -> Self {
      Self {
         pending: mem::ManuallyDrop::new(value),
      }
   }
   #[inline(always)]
   const fn init(value: T) -> Self {
      Self {
         init: mem::ManuallyDrop::new(value),
      }
   }
   #[inline(always)]
   unsafe fn drop_pending(&mut self) -> P {
      mem::ManuallyDrop::take(unsafe { &mut self.pending })
   }

   #[inline(always)]
   unsafe fn drop_init(&mut self) -> T {
      mem::ManuallyDrop::take(unsafe { &mut self.init })
   }
}

struct EditSanitizer<'a, P, T> {
   state: &'a mut TOnceState<P, T>,
   guard: OnceGuard<'a>,
   taken: bool,
}

impl<'a, P, T> EditSanitizer<'a, P, T> {
   #[inline(always)]
   fn new(state: &'a UnsafeCell<TOnceState<P, T>>, guard: OnceGuard<'a>) -> Self {
      Self {
         state: unsafe { &mut *state.get() },
         taken: false,
         guard,
      }
   }

   #[inline(always)]
   unsafe fn take_parameter(&mut self) -> P {
      debug_assert!(!self.taken, "Parameter already taken");
      self.taken = true;
      unsafe { self.state.drop_pending() }
   }
   #[inline(always)]
   unsafe fn ref_parameter(&self) -> &P {
      unsafe { &self.state.pending }
   }
   #[inline(always)]
   unsafe fn commit(self, value: T) -> &'a mut T {
      unsafe {
         if !self.taken {
            _ = self.state.drop_pending();
         }
         *self.state = TOnceState::init(value);
         self.guard.commit_forgotten();
         let ptr = self.state as *mut TOnceState<P, T>;
         mem::forget(self);
         &mut (*ptr).init
      }
   }
}

#[cfg(debug_assertions)]
impl<P, T> Drop for EditSanitizer<'_, P, T> {
   #[inline(always)]
   fn drop(&mut self) {
      assert!(!self.taken, "Parameter taken on return, no value in cell");
   }
}

/// A thread-safe cell which can be written to only once using a parameterized initializer.
///
/// This structure provides safe initialization for values that might be accessed
/// concurrently by multiple threads. It ensures that the initialization logic
/// runs only once, even if multiple threads attempt to initialize the value simultaneously.
///
/// It uses atomic operations and `parking_lot`'s futex-based synchronization for
/// efficient blocking when necessary.
pub struct TOnce<P, T> {
   value: UnsafeCell<TOnceState<P, T>>,
   lock: OnceLock,
}

impl<P, T> TOnce<P, T> {
   /// Creates a new, uninitialized `TOnce` cell with the given parameter.
   #[inline]
   #[must_use]
   pub const fn new(param: P) -> Self {
      Self {
         lock: OnceLock::new(),
         value: UnsafeCell::new(TOnceState::pending(param)),
      }
   }

   /// Creates a new `TOnce` cell that is already initialized with the given value, bypassing the parameter.
   #[inline]
   #[must_use]
   pub const fn with_value(value: T) -> Self {
      Self {
         lock: OnceLock::done(),
         value: UnsafeCell::new(TOnceState::init(value)),
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

   /// Attempts to initialize the cell with `value` without blocking, ignoring the parameter.
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
      unsafe {
         let edit = EditSanitizer::new(&self.value, guard);
         let v = edit.commit(value);
         Ok(v)
      }
   }

   /// Replaces the cell's value, returning the old value if initialized.
   ///
   /// - If uninitialized, discards the parameter, sets the value to `value` and returns `None`.
   /// - If initialized, replaces the existing value with `value` and returns the old value.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks.
   #[inline]
   pub fn replace_mut(&mut self, value: T) -> Option<T> {
      if self.lock.set_done() {
         // Was uninitialized, now set to done. Replace with the new value.
         unsafe {
            mem::replace(self.value.get_mut(), TOnceState::init(value)).drop_pending();
         }
         None
      } else {
         // Was already initialized. Replace the existing value.
         Some(unsafe { mem::replace(self.get_unchecked_mut(), value) })
      }
   }

   /// Gets a mutable reference, initializing with `value` if needed.
   ///
   /// - If initialized, returns a mutable reference to the existing value.
   /// - If uninitialized, discards the parameter, initializes it with `value` and returns a mutable reference.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks.
   #[inline]
   pub fn get_mut_or_set(&mut self, value: T) -> &mut T {
      if self.lock.set_done() {
         // Was uninitialized, now set to done. Replace with the new value.
         unsafe {
            mem::replace(self.value.get_mut(), TOnceState::init(value)).drop_pending();
         }
      }
      // SAFETY: The cell is guaranteed to be initialized here, either previously
      // or by the call above, and we have exclusive access.
      unsafe { self.get_unchecked_mut() }
   }

   /// Gets a mutable reference, initializing with `Default::default()` if needed.
   ///
   /// - If initialized, returns a mutable reference to the existing value.
   /// - If uninitialized, discards the parameter, initializes it with `T::default()` and returns a mutable reference.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks.
   #[inline]
   pub fn get_mut_or_default(&mut self) -> &mut T
   where
      T: Default,
   {
      if self.lock.set_done() {
         // Was uninitialized, now set to done. Replace with the default value.
         unsafe {
            mem::replace(self.value.get_mut(), TOnceState::init(T::default())).drop_pending();
         }
      }
      // SAFETY: The cell is guaranteed to be initialized here, either previously
      // or by the call above, and we have exclusive access.
      unsafe { self.get_unchecked_mut() }
   }

   /// Returns a reference to the value without checking if it's initialized.
   ///
   /// # Safety
   ///
   /// Calling this method on an uninitialized `TOnce` cell is *undefined behavior*.
   /// The caller must ensure the cell is initialized, e.g., by calling `is_done()` or `get()`.
   #[inline]
   pub unsafe fn get_unchecked(&self) -> &T {
      debug_assert!(self.is_done(), "get_unchecked called on uninitialized Once");
      // SAFETY: The caller guarantees that the cell is initialized.
      unsafe { &(*self.value.get()).init }
   }

   /// Returns a mutable reference to the value without checking if it's initialized.
   ///
   /// # Safety
   ///
   /// Calling this method on an uninitialized `TOnce` cell is *undefined behavior*.
   /// The caller must ensure the cell is initialized and that they have exclusive access.
   #[inline]
   pub unsafe fn get_unchecked_mut(&mut self) -> &mut T {
      debug_assert!(
         self.is_done(),
         "get_unchecked_mut called on uninitialized Once"
      );
      // SAFETY: The caller guarantees that the cell is initialized and we have exclusive access.
      unsafe { &mut (*self.value.get()).init }
   }

   /// Takes the value out of the cell, leaving it uninitialized with the given parameter.
   ///
   /// Returns `Some(value)` if the cell was initialized, `None` otherwise.
   /// Requires exclusive access (`&mut self`), so it never blocks.
   #[inline]
   pub fn take(&mut self, param: P) -> Result<T, P> {
      if !self.lock.set_uninit() {
         return Err(param);
      }
      let mut mref = mem::replace(self.value.get_mut(), TOnceState::pending(param));
      Ok(unsafe { mref.drop_init() })
   }

   /// Initializes the cell with `value`, ignoring the parameter. Blocks if another thread is initializing.
   ///
   /// - If uninitialized, discards the parameter, initializes it with `value` and returns `Ok(())`.
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
   /// - If uninitialized, discards the parameter, initializes with `value` and returns `Ok(&value)`.
   /// - If already initialized, returns `Err((&current_value, value))`.
   ///
   /// Guarantees the cell is initialized upon return.
   #[inline]
   pub fn try_insert(&self, value: T) -> Result<&T, (&T, T)> {
      // `get_or_init` ensures initialization. We use `value` only if the cell was empty.
      let mut value_opt = Some(value);
      let res_ref = self.get_or_init(|_p| value_opt.take().unwrap());
      match value_opt {
         None => Ok(res_ref), // Our value was used for initialization
         Some(original_value) => Err((res_ref, original_value)), // Someone else initialized it first
      }
   }

   /// Gets the value, initializing with `f(param)` if needed. Blocks if needed.
   ///
   /// - If initialized, returns a reference to the existing value.
   /// - If uninitialized, calls `f(param)`, stores the result, and returns a reference.
   ///
   /// If multiple threads call this concurrently, only one `f(param)` execution happens.
   #[inline]
   pub fn get_or_init<F>(&self, f: F) -> &T
   where
      F: FnOnce(P) -> T,
   {
      if let Some(value) = self.get() {
         return value;
      }
      // Cold path: needs initialization
      self.initialize(f);
      // SAFETY: initialize ensures the value is now initialized.
      unsafe { self.get_unchecked() }
   }

   /// Gets a mutable reference, initializing with `f(param)` if needed.
   ///
   /// - If initialized, returns a mutable reference to the existing value.
   /// - If uninitialized, calls `f(param)`, stores the result, and returns a mutable reference.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks.
   #[inline]
   pub fn get_mut_or_init<F>(&mut self, f: F) -> &mut T
   where
      F: FnOnce(P) -> T,
   {
      if self.is_done() {
         // Already initialized.
      } else if let Some(guard) = self.lock.try_lock() {
         // We got the lock (because is_done was false and no one else had it). Initialize it.
         // SAFETY: We hold the lock, exclusive access to initialize.
         unsafe {
            let mut edit = EditSanitizer::new(&self.value, guard);
            let value = f(edit.take_parameter());
            edit.commit(value);
         }
      } else {
         // This case should theoretically not happen with &mut self,
         // as try_lock should succeed if !is_done().
         // If it did, it implies a logic error or unexpected concurrent access.
         unreachable!("Could not lock for init despite having exclusive access");
      }

      // SAFETY: The cell is guaranteed to be initialized now, and we have exclusive access.
      unsafe { self.get_unchecked_mut() }
   }

   /// Gets the value, initializing with fallible `f(param)` if needed. Blocks if needed.
   ///
   /// - If initialized, returns `Ok(&value)`.
   /// - If uninitialized, calls `f(param)`:
   ///     - On `Ok(value)`, initializes the cell and returns `Ok(&value)`.
   ///     - On `Err(e)`, returns `Err(e)` and leaves the cell uninitialized.
   ///
   /// If multiple threads call this concurrently, only one `f(param)` execution happens.
   pub fn get_or_try_init<F, E>(&self, f: F) -> Result<&T, E>
   where
      F: FnOnce(&P) -> Result<T, E>,
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

   /// Gets a mutable reference, initializing with fallible `f(param)` if needed.
   ///
   /// - If initialized, returns `Ok(&mut value)`.
   /// - If uninitialized, calls `f(param)`:
   ///     - On `Ok(value)`, initializes the cell and returns `Ok(&mut value)`.
   ///     - On `Err(e)`, returns `Err(e)` and leaves the cell uninitialized.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks (initialization happens inline).
   pub fn get_mut_or_try_init<F, E>(&mut self, f: F) -> Result<&mut T, E>
   where
      F: FnOnce(&P) -> Result<T, E>,
   {
      if let Some(guard) = self.lock.try_lock() {
         // We got the lock. Try to initialize.
         unsafe {
            let edit = EditSanitizer::new(&self.value, guard);
            let value = f(edit.ref_parameter())?;
            edit.commit(value);
         }
      }
      // SAFETY: The cell is guaranteed to be initialized now (or we returned Err),
      // and we have exclusive access.
      Ok(unsafe { self.get_unchecked_mut() })
   }

   /// Gets the value, initializing asynchronously with `f(param)` if needed. Blocks if needed.
   ///
   /// - If initialized, returns a reference to the existing value.
   /// - If uninitialized, awaits `f(param)`, stores the result, and returns a reference.
   ///
   /// If multiple tasks call this concurrently, only one `f(param)` execution happens.
   #[inline]
   pub async fn get_or_init_async<F, Fut>(&self, f: F) -> &T
   where
      F: FnOnce(&P) -> Fut,
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

   /// Gets a mutable reference, initializing asynchronously with `f(param)` if needed.
   ///
   /// - If initialized, returns a mutable reference to the existing value.
   /// - If uninitialized, awaits `f(param)`, stores the result, and returns a mutable reference.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks (initialization happens inline).
   #[inline]
   pub async fn get_mut_or_init_async<F, Fut>(&mut self, f: F) -> &mut T
   where
      F: FnOnce(&P) -> Fut,
      Fut: Future<Output = T>,
   {
      if let Some(guard) = self.lock.try_lock() {
         // We got the lock. Try to initialize.
         unsafe {
            let edit = EditSanitizer::new(&self.value, guard);
            let value = f(edit.ref_parameter()).await;
            edit.commit(value);
         }
      }
      // SAFETY: The cell is guaranteed to be initialized now (or we returned Err),
      // and we have exclusive access.
      unsafe { self.get_unchecked_mut() }
   }

   /// Gets the value, initializing asynchronously with fallible `f(param)` if needed. Blocks if needed.
   ///
   /// - If initialized, returns `Ok(&value)`.
   /// - If uninitialized, awaits `f(param)`:
   ///     - On `Ok(value)`, initializes the cell and returns `Ok(&value)`.
   ///     - On `Err(e)`, returns `Err(e)` and leaves the cell uninitialized.
   ///
   /// If multiple tasks call this concurrently, only one `f(param)` execution happens.
   pub async fn get_or_try_init_async<F, Fut, E>(&self, f: F) -> Result<&T, E>
   where
      F: FnOnce(&P) -> Fut,
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

   /// Gets a mutable reference, initializing asynchronously with fallible `f(param)` if needed.
   ///
   /// - If initialized, returns `Ok(&mut value)`.
   /// - If uninitialized, awaits `f(param)`:
   ///     - On `Ok(value)`, initializes the cell and returns `Ok(&mut value)`.
   ///     - On `Err(e)`, returns `Err(e)` and leaves the cell uninitialized.
   ///
   /// Requires exclusive access (`&mut self`), so it never blocks (initialization happens inline).
   pub async fn get_mut_or_try_init_async<F, Fut, E>(&mut self, f: F) -> Result<&mut T, E>
   where
      F: FnOnce(&P) -> Fut,
      Fut: Future<Output = Result<T, E>>,
   {
      if let Some(guard) = self.lock.try_lock() {
         // We got the lock. Try to initialize.
         unsafe {
            let edit = EditSanitizer::new(&self.value, guard);
            let value = f(edit.ref_parameter()).await?;
            edit.commit(value);
         }
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
      F: FnOnce(&P) -> Fut,
      Fut: Future<Output = T>,
   {
      let Some(guard) = self.lock.lock_async().await else {
         return; // Another task initialized it while we waited
      };
      // SAFETY: We hold the lock, exclusive access to initialize the value.
      unsafe {
         let edit = EditSanitizer::new(&self.value, guard);
         let value = f(edit.ref_parameter()).await;
         edit.commit(value);
      }
   }

   /// Cold path for `get_or_try_init_async`. Acquires lock asynchronously and awaits fallible initializer.
   #[cold]
   async fn try_initialize_async<Fn, Fut, E>(&self, f: Fn) -> Result<(), E>
   where
      Fn: FnOnce(&P) -> Fut,
      Fut: Future<Output = Result<T, E>>,
   {
      let Some(guard) = self.lock.lock_async().await else {
         return Ok(()); // Another task initialized it while we waited
      };
      unsafe {
         let edit = EditSanitizer::new(&self.value, guard);
         let value = f(edit.ref_parameter()).await?;
         edit.commit(value);
      }
      Ok(())
   }

   /// Cold path for `get_or_init`. Acquires lock and calls initializer.
   #[cold]
   fn initialize<F>(&self, f: F)
   where
      F: FnOnce(P) -> T,
   {
      let Some(guard) = self.lock.lock() else {
         return; // Another thread initialized it while we waited for the lock
      };
      // SAFETY: We hold the lock, exclusive access to initialize the value.
      unsafe {
         let mut edit = EditSanitizer::new(&self.value, guard);
         let value = f(edit.take_parameter());
         edit.commit(value);
      }
   }

   /// Cold path for `get_or_try_init`. Acquires lock and calls fallible initializer.
   #[cold]
   fn try_initialize<F, E>(&self, f: F) -> Result<(), E>
   where
      F: FnOnce(&P) -> Result<T, E>,
   {
      let Some(guard) = self.lock.lock() else {
         return Ok(()); // Another thread initialized it while we waited for the lock
      };
      unsafe {
         let edit = EditSanitizer::new(&self.value, guard);
         let value = f(edit.ref_parameter())?;
         edit.commit(value);
      }
      Ok(())
   }
}

// --- Trait Implementations ---

impl<P, T> From<Option<T>> for TOnce<P, T>
where
   P: Default,
{
   /// Creates an initialized `TOnce` from `Some(value)` or an uninitialized one from `None` with a default parameter.
   fn from(value: Option<T>) -> Self {
      match value {
         Some(value) => Self::with_value(value),
         None => Self::new(P::default()),
      }
   }
}

impl<P, T> From<Result<T, P>> for TOnce<P, T> {
   /// Creates an initialized `TOnce` from `Ok(value)` or an uninitialized one from `Err(param)` with the parameter.
   fn from(value: Result<T, P>) -> Self {
      match value {
         Ok(value) => Self::with_value(value),
         Err(param) => Self::new(param),
      }
   }
}

// SAFETY:
// `&TOnce<P, T>` is `Sync` if `&T` is `Sync` (requiring `T: Sync`)
// and if the initialization mechanism is thread-safe (which it is).
// `T: Send` is also required because a value provided by one thread
// might be read or dropped by another.
// `P: Sync` is required because the parameter might be accessed by multiple threads.
unsafe impl<P: Sync + Send, T: Send> Sync for TOnce<P, T> {}
// SAFETY:
// `TOnce<P, T>` is `Send` if both `P` and `T` are `Send`, as the ownership of both
// can be transferred across threads via initialization or `take()`.
unsafe impl<P: Send, T: Send> Send for TOnce<P, T> {}

impl<P: Default, T> Default for TOnce<P, T> {
   /// Creates a new, uninitialized `TOnce` cell with default parameter.
   #[inline]
   fn default() -> Self {
      Self::new(P::default())
   }
}

impl<P, T: fmt::Display> fmt::Display for TOnce<P, T> {
   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      match self.get() {
         Some(v) => fmt::Display::fmt(v, f),
         None => f.write_str("<uninit>"),
      }
   }
}

impl<P, T: fmt::Debug> fmt::Debug for TOnce<P, T> {
   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      let mut d = f.debug_tuple("Once");
      match self.get() {
         Some(v) => d.field(v),
         None => d.field(&format_args!("<uninit>")),
      };
      d.finish()
   }
}

impl<P: Clone, T: Clone> Clone for TOnce<P, T> {
   /// Clones the `TOnce` cell.
   ///
   /// If the original cell is initialized, the clone will be initialized
   /// with a cloned value. If the original is uninitialized, the clone
   /// will also be uninitialized with a cloned parameter.
   #[inline]
   fn clone(&self) -> Self {
      if let Some(value) = self.get() {
         Self::with_value(value.clone())
      } else {
         let Some(_guard) = self.lock.lock() else {
            return Self::with_value(
               self
                  .get()
                  .expect("is_done() was false but value is init")
                  .clone(),
            );
         };
         Self::new(unsafe { (*(*self.value.get()).pending).clone() })
      }
   }
}

impl<T> From<T> for TOnce<(), T> {
   /// Creates a new, initialized `TOnce` cell from the given value.
   #[inline]
   fn from(value: T) -> Self {
      Self::with_value(value)
   }
}

impl<P, T: PartialEq> PartialEq for TOnce<P, T> {
   /// Checks if two `TOnce` cells are equal.
   ///
   /// They are equal if both are uninitialized, or if both are initialized
   /// and their contained values are equal according to `PartialEq`.
   #[inline]
   fn eq(&self, other: &Self) -> bool {
      self.get() == other.get()
   }
}

impl<P, T: Eq> Eq for TOnce<P, T> {}

impl<P, T> Drop for TOnce<P, T> {
   #[inline]
   fn drop(&mut self) {
      unsafe {
         if self.is_done() {
            self.value.get_mut().drop_init();
         } else {
            self.value.get_mut().drop_pending();
         }
      }
   }
}
