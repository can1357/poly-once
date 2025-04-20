# poly-once

[![Crates.io](https://img.shields.io/crates/v/poly-once.svg)](https://crates.io/crates/poly-once)
[![Docs.rs](https://docs.rs/poly-once/badge.svg)](https://docs.rs/poly-once)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A thread-safe cell providing an initialization primitive similar to `std::sync::OnceLock` but with a lock model that works with both sync and async code.

`poly-once` provides an `Once<T>` type for safe, one-time initialization of values, ensuring that initialization logic runs only once, even under concurrent access from multiple threads or async tasks. It leverages `parking_lot_core` for efficient blocking synchronization.

## Features

- **Thread-Safe:** Safely initialize and access values from multiple threads.
- **Sync Initialization:** Initialize values using standard closures (`get_or_init`, `get_or_try_init`).
- **Async Initialization:** Initialize values using `async fn` or `Future`s (`get_or_init_async`, `get_or_try_init_async`).
- **Lazy Initialization:** Values are initialized only when first accessed.
- **Fallible Initialization:** Supports initialization functions that can return `Result`.
- **Efficient Blocking:** Uses `parking_lot_core` for low-overhead synchronization when blocking is necessary.
- **Small footprint:** The overhead is only 4 bytes per instance due to the use of parking lot, making it suitable for entities that are created used very frequently.
- **`no_std` Compatibility:** Can be used in `no_std` environments (requires disabling default features if `tokio` dependency is not desired).

## Usage

Add `poly-once` to your `Cargo.toml`:

```toml
[dependencies]
poly-once = "1" # Use the latest version
```

### Basic Sync Initialization

```rust
use poly_once::Once;
use std::sync::atomic::{AtomicUsize, Ordering};

static COUNTER: AtomicUsize = AtomicUsize::new(0);
static DATA: Once<String> = Once::new();

fn get_data() -> &'static str {
    DATA.get_or_init(|| {
        // This closure runs only once
        COUNTER.fetch_add(1, Ordering::Relaxed);
        println!("Initializing data...");
        // Simulate work
        std::thread::sleep(std::time::Duration::from_millis(50));
        "Expensive data".to_string()
    })
}

fn main() {
    let threads: Vec<_> = (0..5).map(|_| {
        std::thread::spawn(|| {
            println!("Thread access: {}", get_data());
        })
    }).collect();

    for t in threads {
        t.join().unwrap();
    }

    assert_eq!(DATA.get(), Some(&"Expensive data".to_string()));
    assert_eq!(COUNTER.load(Ordering::Relaxed), 1); // Initializer ran only once
    println!("Final data: {}", get_data());
}
```

### Async Initialization

```rust
use poly_once::Once;
use std::sync::atomic::{AtomicUsize, Ordering};
use tokio::time::{sleep, Duration};

static COUNTER: AtomicUsize = AtomicUsize::new(0);
static ASYNC_DATA: Once<String> = Once::new();

async fn get_async_data() -> &'static String {
    ASYNC_DATA.get_or_init_async(async {
        // This async block runs only once
        COUNTER.fetch_add(1, Ordering::Relaxed);
        println!("Initializing async data...");
        sleep(Duration::from_millis(50)).await;
        "Async expensive data".to_string()
    }).await
}

#[tokio::main]
async fn main() {
    let tasks: Vec<_> = (0..5).map(|_| {
        tokio::spawn(async {
            println!("Task access: {}", get_async_data().await);
        })
    }).collect();

    for t in tasks {
        t.await.unwrap();
    }

    assert_eq!(ASYNC_DATA.get(), Some(&"Async expensive data".to_string()));
    assert_eq!(COUNTER.load(Ordering::Relaxed), 1); // Initializer ran only once
    println!("Final async data: {}", get_async_data().await);
}
```

### Fallible Initialization

Handles cases where initialization might fail.

```rust
use poly_once::Once;

static MAYBE_DATA: Once<String> = Once::new();

fn try_get_data(fail: bool) -> Result<&'static String, &'static str> {
    MAYBE_DATA.get_or_try_init(|| {
        println!("Attempting initialization (fail={})...", fail);
        if fail {
            Err("Initialization failed!")
        } else {
            Ok("Successfully initialized".to_string())
        }
    })
}

fn main() {
    // First attempt fails
    match try_get_data(true) {
        Ok(_) => panic!("Should have failed"),
        Err(e) => println!("Caught error: {}", e),
    }
    assert!(!MAYBE_DATA.is_done()); // Still uninitialized

    // Second attempt succeeds
    match try_get_data(false) {
        Ok(data) => println!("Got data: {}", data),
        Err(_) => panic!("Should have succeeded"),
    }
    assert!(MAYBE_DATA.is_done());
    assert_eq!(MAYBE_DATA.get(), Some(&"Successfully initialized".to_string()));

    // Subsequent attempts (even failing ones) return the initialized value
    match try_get_data(true) {
        Ok(data) => println!("Got data again: {}", data),
        Err(_) => panic!("Should have returned existing data"),
    }
}
```

## Cargo Features

`poly-once` uses feature flags to enable asynchronous support and configure dependencies.

- **`async-tokio`**:

  - Enables async initialization methods.
  - Compatible with any `tokio` runtime, dropping the requirement of `tokio::task::block_in_place` in exchange for a less efficient implementation.

- **`async-tokio-mt`**:
  - Enables async initialization methods.
  - Uses the multi-threaded `tokio` runtime. Requires `tokio` with the `rt` and `rt-multi-thread` features.

**`no_std` Usage:**

To use `poly-once` in a `no_std` environment _without_ requiring `tokio`, disable the default features:

```toml
[dependencies]
poly-once = { version = "1", default-features = false }
```

This will provide less efficient asyncronous methods without the support of the runtime.

## License

Licensed under the MIT License. See the [LICENSE](LICENSE) file for details.

## Contributing

Contributions are welcome! Please feel free to submit pull requests or open issues on the [repository](https://github.com/can1357/poly-once).
