//! A collection of thread-safe, lock-free "once" cells for one-time initialization.
//!
//! This crate provides two main types for one-time initialization patterns:
//!
//! - [`Once<T>`]: A standard once cell that can be written to only once.
//! - [`TOnce<P, T>`]: A parameterized once cell that stores a parameter and transforms it
//!   into the final value on first access.
//!
//! Both types are thread-safe and use atomic operations with `parking_lot`'s futex-based
//! synchronization for efficient blocking when necessary. They guarantee that initialization
//! logic runs exactly once, even when multiple threads attempt concurrent initialization.
//!
//! # Features
//!
//! - **Lock-free fast path**: Reading initialized values requires no synchronization.
//! - **Efficient blocking**: Uses futex-based parking when waiting for initialization.
//! - **Async support**: Both types support async initialization with futures.
//! - **Fallible initialization**: Support for initialization functions that can fail.
//! - **No heap allocation**: Stack-based storage with no dynamic memory allocation.
//!
//! # Examples
//!
//! ## Basic Once Cell
//!
//! ```rust
//! use poly_once::Once;
//!
//! static CONFIG: Once<String> = Once::new();
//!
//! // Initialize the value
//! CONFIG.get_or_init(|| "production".to_string());
//!
//! // Subsequent calls return the same value without re-running the initializer
//! assert_eq!(CONFIG.get(), Some(&"production".to_string()));
//! ```
//!
//! ## Parameterized Once Cell
//!
//! ```rust
//! use poly_once::TOnce;
//!
//! // Store a path, transform it to a loaded config on first access
//! let config_cell = TOnce::new("/etc/app.conf");
//!
//! let config = config_cell.get_or_init(|path| {
//!     // This runs only once, even if called from multiple threads
//!     std::fs::read_to_string(path).unwrap_or_default()
//! });
//! ```

/// Standard once cell implementation.
mod once;

/// Internal synchronization state management.
mod state;

/// Parameterized once cell implementation.
mod transform_once;

pub use once::Once;
pub use transform_once::TOnce;
