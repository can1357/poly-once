use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use poly_once::Once;

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
      value.push('!');
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
      value.push('!');
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
               format!("init {current_count}")
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
               Ok::<_, &str>(format!("mut async ok {current_count}"))
            }
         })
         .await;
      assert!(result.is_ok());
      let value = result.unwrap();
      assert_eq!(value, "mut async ok 0");
      assert_eq!(counter_ok.load(Ordering::SeqCst), 1);
      value.push('!');
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
            Err::<String, _>(format!("mut async fail {current_count}"))
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
               Ok::<_, String>(format!("mut async retry ok {current_count}"))
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
