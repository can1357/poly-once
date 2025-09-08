//! Internal synchronization primitives for once cells.
//!
//! This module provides the low-level synchronization state management used by
//! both `Once` and `TOnce`. It implements a custom state machine using atomic
//! operations and futex-based waiting via `parking_lot_core`.
//!
//! The state is packed into a single `AtomicU8` with the following layout:
//! - Bit 0: DONE - Cell is initialized
//! - Bit 1: LOCKED - Cell is locked for initialization
//! - Bit 2: WAITING - At least one thread is waiting
//! - Bits 3-7: EPOCH - Generation counter to prevent ABA issues
//!
//! This design allows for lock-free reads of initialized values while providing
//! efficient blocking for threads waiting on initialization.

use core::mem;
use core::sync::atomic::{self, AtomicU8, Ordering};

use parking_lot_core::{DEFAULT_PARK_TOKEN, DEFAULT_UNPARK_TOKEN};

/// Atomic state management for the `Once` cell.
#[repr(transparent)]
pub struct OnceLock(AtomicU8);

impl OnceLock {
   /// Bit flag: Cell is initialized.
   const DONE: u8 = 1;
   /// Bit flag: Cell is locked for initialization.
   const LOCKED: u8 = 2;
   /// Bit flag: At least one thread is waiting for initialization.
   const WAITING: u8 = 4;
   /// Start of epoch bits (used to detect ABA issues, although primarily for waits).
   const EPOCH_1: u8 = 8;
   /// Mask for epoch bits.
   const EPOCH_MASK: u8 = !(Self::DONE | Self::LOCKED | Self::WAITING);

   /// Calculates the next epoch value based on the current state.
   #[inline(always)]
   const fn next_epoch(current_state: u8) -> u8 {
      (current_state & Self::EPOCH_MASK).wrapping_add(Self::EPOCH_1) & Self::EPOCH_MASK
   }

   /// Creates a new state representing an uninitialized cell.
   #[inline]
   pub(crate) const fn new() -> Self {
      Self(AtomicU8::new(0)) // Initial state: 0 (no flags set)
   }

   /// Creates a new state representing an initialized cell.
   #[inline]
   pub(crate) const fn done() -> Self {
      Self(AtomicU8::new(Self::DONE)) // Initial state: DONE flag set
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
   fn wait(&self, expected_state: u8) {
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
   pub(crate) fn set_done(&self) -> bool {
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
   pub(crate) fn set_uninit(&self) -> bool {
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
   pub(crate) fn is_done(&self, ordering: Ordering) -> bool {
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
   fn lock_step(&self, nowait: bool) -> Result<Option<OnceGuard<'_>>, u8> {
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
         }
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
         }
         // Lock is held, and either we shouldn't wait (`nowait`) or WAITING is already set.
         // Return Err with the current state we observed.
         return Err(current_state);
      }
   }

   /// Acquires the initialization lock, blocking if necessary.
   ///
   /// Returns `Some(guard)` if the lock was acquired (cell was not initialized).
   /// Returns `None` if the cell was already initialized.
   #[inline]
   pub(crate) fn lock(&self) -> Option<OnceGuard<'_>> {
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
   pub(crate) async fn lock_async(&self) -> Option<OnceGuard<'_>> {
      #[allow(clippy::never_loop)]
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
   pub(crate) fn try_lock(&self) -> Option<OnceGuard<'_>> {
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
pub struct OnceGuard<'a> {
   state: &'a OnceLock,
}

impl<'a> OnceGuard<'a> {
   /// Creates a new guard. Assumes the `LOCKED` flag is already set on `state`.
   #[inline(always)]
   pub(crate) const fn new(state: &'a OnceLock) -> Self {
      Self { state }
   }

   /// Marks initialization as complete (`DONE`), consumes the guard, and notifies waiters.
   /// Returns `true` if the state was successfully changed from !DONE to DONE.
   #[inline(always)]
   pub(crate) fn commit(self) -> bool {
      let success = self.state.set_done();
      mem::forget(self); // Prevent Drop from running (which would reset state)
      success
   }

   /// Marks initialization as complete (`DONE`), consumes the guard, and notifies waiters.
   /// Caller should forget the guard after calling this.
   #[inline(always)]
   pub(crate) unsafe fn commit_forgotten(&self) {
      self.state.set_done();
   }
}

impl Drop for OnceGuard<'_> {
   /// Called if initialization is cancelled (e.g., due to panic or error in `try_init`).
   /// Resets the state to uninitialized (clears `LOCKED`), allowing another thread to try.
   #[inline(always)]
   fn drop(&mut self) {
      self.state.set_uninit(); // Resets state and notifies waiters
   }
}
