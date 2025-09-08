use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use poly_once::TOnce;

#[test]
fn test_new_is_not_done() {
   let once: TOnce<(), i32> = TOnce::new(());
   assert!(!once.is_done());
   assert_eq!(once.get(), None);
}

#[test]
fn test_with_value_is_done() {
   let once = TOnce::<(), i32>::with_value(42);
   assert!(once.is_done());
   assert_eq!(once.get(), Some(&42));
}

#[test]
fn test_get_or_init() {
   let once: TOnce<i32, i32> = TOnce::new(10);
   let counter = AtomicUsize::new(0);
   let value = once.get_or_init(|p| {
      counter.fetch_add(1, Ordering::SeqCst);
      p * 4 + 2
   });
   assert_eq!(value, &42);
   assert!(once.is_done());
   assert_eq!(counter.load(Ordering::SeqCst), 1);

   // Second call should not execute the closure
   let value = once.get_or_init(|_p| {
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
   let once: TOnce<(), i32> = TOnce::new(());
   once.get_or_init(|()| {
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
   let once: TOnce<(), i32> = TOnce::new(());

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
   let once: TOnce<(), i32> = TOnce::new(());

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
   let once_ok: TOnce<i32, i32> = TOnce::new(21);
   let counter_ok = AtomicUsize::new(0);

   // Should initialize with Ok value
   let result = once_ok.get_or_try_init(|p| {
      counter_ok.fetch_add(1, Ordering::SeqCst);
      Ok::<_, &str>(p * 2)
   });
   assert_eq!(result, Ok(&42));
   assert!(once_ok.is_done());
   assert_eq!(counter_ok.load(Ordering::SeqCst), 1);

   // Second call should return existing value, not run closure
   let result = once_ok.get_or_try_init(|p| {
      counter_ok.fetch_add(1, Ordering::SeqCst);
      Ok::<_, &str>(p * 10) // Different value to check it's not used
   });
   assert_eq!(result, Ok(&42));
   assert_eq!(counter_ok.load(Ordering::SeqCst), 1); // Counter didn't increase

   // Test initialization failure
   let once_err: TOnce<i32, i32> = TOnce::new(100);
   let counter_err = AtomicUsize::new(0);
   let result = once_err.get_or_try_init(|_p| {
      counter_err.fetch_add(1, Ordering::SeqCst);
      Err::<i32, _>("init error")
   });
   assert_eq!(result, Err("init error"));
   assert!(!once_err.is_done()); // Should remain uninitialized
   assert_eq!(counter_err.load(Ordering::SeqCst), 1);

   // Try initializing again after failure, this time successfully
   let result = once_err.get_or_try_init(|p| {
      counter_err.fetch_add(1, Ordering::SeqCst);
      Ok::<_, &str>(p / 2 + 5)
   });
   assert_eq!(result, Ok(&55));
   assert!(once_err.is_done());
   assert_eq!(counter_err.load(Ordering::SeqCst), 2); // Counter increased again
}

#[test]
fn test_take() {
   let mut once = TOnce::<i32, i32>::with_value(42);
   assert!(once.is_done());
   assert_eq!(once.take(99), Ok(42));
   assert!(!once.is_done());
   assert_eq!(once.get(), None);
   assert_eq!(once.take(88), Err(88)); // Taking again returns the param back

   // Taking from initially empty cell
   let mut empty: TOnce<i32, i32> = TOnce::new(77);
   assert!(!empty.is_done());
   assert_eq!(empty.take(66), Err(66)); // Returns the param back
   assert!(!empty.is_done());
}

#[test]
fn test_multi_thread_get_or_init() {
   let once = Arc::new(TOnce::new(21));
   let init_counter = Arc::new(AtomicUsize::new(0));
   let threads: Vec<_> = (0..10)
      .map(|_| {
         let once_clone = Arc::clone(&once);
         let counter_clone = Arc::clone(&init_counter);
         thread::spawn(move || {
            // Simulate some delay/contention
            thread::sleep(Duration::from_millis(10));
            *once_clone.get_or_init(|p| {
               counter_clone.fetch_add(1, Ordering::SeqCst);
               // More delay during initialization
               thread::sleep(Duration::from_millis(20));
               p * 2
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
   let once = Arc::new(TOnce::<(), i32>::new(()));
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
   let once_some: TOnce<(), i32> = TOnce::from(Some(42));
   assert!(once_some.is_done());
   assert_eq!(once_some.get(), Some(&42));

   let once_none: TOnce<(), i32> = TOnce::from(None);
   assert!(!once_none.is_done());
   assert_eq!(once_none.get(), None);
}

#[test]
fn test_replace_mut() {
   // Replace in initialized cell
   let mut once = TOnce::<(), i32>::with_value(42);
   assert_eq!(once.get(), Some(&42));
   assert_eq!(once.replace_mut(84), Some(42));
   assert_eq!(once.get(), Some(&84));
   assert!(once.is_done());

   // Replace in uninitialized cell
   let mut empty: TOnce<(), i32> = TOnce::new(());
   assert_eq!(empty.get(), None);
   assert_eq!(empty.replace_mut(42), None);
   assert_eq!(empty.get(), Some(&42));
   assert!(empty.is_done());
}

#[test]
fn test_get_mut_or_set() {
   let mut once: TOnce<(), String> = TOnce::new(());

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
   let mut once: TOnce<(), Vec<i32>> = TOnce::new(()); // Vec::default() is empty vec

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
   let once: TOnce<(), i32> = TOnce::new(());

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
}

#[test]
fn test_get_mut_or_init() {
   let mut once: TOnce<i32, String> = TOnce::new(100);
   let counter = AtomicUsize::new(0);

   // First call initializes
   {
      let value = once.get_mut_or_init(|p| {
         counter.fetch_add(1, Ordering::SeqCst);
         format!("init{p}")
      });
      assert_eq!(value, "init100");
      assert_eq!(counter.load(Ordering::SeqCst), 1);
      value.push_str("ial");
   }
   assert_eq!(once.get(), Some(&String::from("init100ial")));
   assert!(once.is_done());

   // Second call gets existing value, closure not called
   {
      let value = once.get_mut_or_init(|_p| {
         counter.fetch_add(1, Ordering::SeqCst);
         panic!("Should not be called");
      });
      assert_eq!(value, "init100ial");
      assert_eq!(counter.load(Ordering::SeqCst), 1); // Counter unchanged
      value.push_str("ized");
   }
   assert_eq!(once.get(), Some(&String::from("init100ialized")));
   assert!(once.is_done());
}

#[test]
fn test_get_mut_or_try_init() {
   let mut once_ok: TOnce<&str, String> = TOnce::new("param");
   let counter_ok = AtomicUsize::new(0);

   // First call initializes successfully
   {
      let result = once_ok.get_mut_or_try_init(|p| {
         counter_ok.fetch_add(1, Ordering::SeqCst);
         Ok::<_, &str>(format!("{p}_ok"))
      });
      assert!(result.is_ok());
      let value = result.unwrap();
      assert_eq!(value, "param_ok");
      assert_eq!(counter_ok.load(Ordering::SeqCst), 1);
      value.push_str("ay");
   }
   assert_eq!(once_ok.get(), Some(&String::from("param_okay")));
   assert!(once_ok.is_done());

   // Second call gets existing value, closure not called
   {
      let result = once_ok.get_mut_or_try_init(|_p| {
         counter_ok.fetch_add(1, Ordering::SeqCst);
         Ok::<_, &str>(String::from("ignored"))
      });
      assert!(result.is_ok());
      let value = result.unwrap();
      assert_eq!(value, "param_okay");
      assert_eq!(counter_ok.load(Ordering::SeqCst), 1); // Counter unchanged
      value.push('!');
   }
   assert_eq!(once_ok.get(), Some(&String::from("param_okay!")));

   // Test initialization failure
   let mut once_err: TOnce<(), String> = TOnce::new(());
   let counter_err = AtomicUsize::new(0);
   let result = once_err.get_mut_or_try_init(|_p| {
      counter_err.fetch_add(1, Ordering::SeqCst);
      Err::<String, _>("fail")
   });
   assert_eq!(result, Err("fail"));
   assert!(!once_err.is_done()); // Remains uninitialized
   assert_eq!(counter_err.load(Ordering::SeqCst), 1);
   assert_eq!(once_err.get(), None);

   // Try again successfully
   {
      let result = once_err.get_mut_or_try_init(|_p| {
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
   let once: TOnce<i32, i32> = TOnce::new(21);
   let counter = Arc::new(AtomicUsize::new(0));

   let value = once
      .get_or_init_async(|p| {
         let counter_clone = Arc::clone(&counter);
         let param = *p;
         async move {
            counter_clone.fetch_add(1, Ordering::SeqCst);
            tokio::time::sleep(Duration::from_millis(10)).await;
            param * 2
         }
      })
      .await;

   assert_eq!(value, &42);
   assert!(once.is_done());
   assert_eq!(counter.load(Ordering::SeqCst), 1);

   // Second call should not execute the future
   let value = once
      .get_or_init_async(|_p| async {
         counter.fetch_add(1, Ordering::SeqCst); // This shouldn't run
         panic!("Should not be called");
      })
      .await;

   assert_eq!(value, &42);
   assert_eq!(counter.load(Ordering::SeqCst), 1); // Counter unchanged
}

#[tokio::test]
async fn test_get_mut_or_init_async() {
   let mut once: TOnce<i32, String> = TOnce::new(77);
   let counter = AtomicUsize::new(0);

   // First call initializes
   {
      let value = once
         .get_mut_or_init_async(|p| {
            let current_count = counter.fetch_add(1, Ordering::SeqCst);
            let param = *p;
            async move {
               tokio::time::sleep(Duration::from_millis(5)).await;
               format!("init {param} {current_count}")
            }
         })
         .await;
      assert_eq!(value, "init 77 0");
      assert_eq!(counter.load(Ordering::SeqCst), 1);
      value.push_str("ial");
   }
   assert_eq!(once.get(), Some(&String::from("init 77 0ial")));
   assert!(once.is_done());

   // Second call gets existing value, future not created/polled
   {
      let value = once
         .get_mut_or_init_async(|_p| async {
            counter.fetch_add(1, Ordering::SeqCst); // Should not run
            panic!("Should not be called");
         })
         .await;
      assert_eq!(value, "init 77 0ial");
      assert_eq!(counter.load(Ordering::SeqCst), 1); // Counter unchanged
      value.push_str("ized");
   }
   assert_eq!(once.get(), Some(&String::from("init 77 0ialized")));
   assert!(once.is_done());
}

#[tokio::test]
async fn test_get_or_try_init_async() {
   let once_ok: TOnce<&str, String> = TOnce::new("async_param");
   let counter_ok = Arc::new(AtomicUsize::new(0));

   // First call initializes successfully
   let result = once_ok
      .get_or_try_init_async(|p| {
         let counter_clone = Arc::clone(&counter_ok);
         let param = (*p).to_string();
         async move {
            counter_clone.fetch_add(1, Ordering::SeqCst);
            tokio::time::sleep(Duration::from_millis(5)).await;
            Ok::<_, &str>(format!("{param} ok"))
         }
      })
      .await;

   assert!(result.is_ok());
   assert_eq!(result.unwrap(), "async_param ok");
   assert!(once_ok.is_done());
   assert_eq!(counter_ok.load(Ordering::SeqCst), 1);

   // Second call gets existing value
   let result = once_ok
      .get_or_try_init_async(|_p| async {
         counter_ok.fetch_add(1, Ordering::SeqCst); // Should not run
         Ok::<_, &str>(String::from("ignored"))
      })
      .await;
   assert!(result.is_ok());
   assert_eq!(result.unwrap(), "async_param ok");
   assert_eq!(counter_ok.load(Ordering::SeqCst), 1); // Counter unchanged

   // Test initialization failure
   let once_err: TOnce<(), String> = TOnce::new(());
   let counter_err = Arc::new(AtomicUsize::new(0));
   let result = once_err
      .get_or_try_init_async(|_p| {
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
      .get_or_try_init_async(|_p| {
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
   let mut once_ok: TOnce<i32, String> = TOnce::new(99);
   let counter_ok = AtomicUsize::new(0);

   // First call initializes successfully
   {
      let result = once_ok
         .get_mut_or_try_init_async(|p| {
            let current_count = counter_ok.fetch_add(1, Ordering::SeqCst);
            let param = *p;
            async move {
               tokio::time::sleep(Duration::from_millis(5)).await;
               Ok::<_, &str>(format!("mut async ok {param} {current_count}"))
            }
         })
         .await;
      assert!(result.is_ok());
      let value = result.unwrap();
      assert_eq!(value, "mut async ok 99 0");
      assert_eq!(counter_ok.load(Ordering::SeqCst), 1);
      value.push('!');
   }
   assert_eq!(once_ok.get(), Some(&String::from("mut async ok 99 0!")));
   assert!(once_ok.is_done());

   // Second call gets existing value
   {
      let result = once_ok
         .get_mut_or_try_init_async(|_p| async {
            counter_ok.fetch_add(1, Ordering::SeqCst); // Should not run
            Ok::<_, &str>(String::from("ignored"))
         })
         .await;
      assert!(result.is_ok());
      let value = result.unwrap();
      assert_eq!(value, "mut async ok 99 0!");
      assert_eq!(counter_ok.load(Ordering::SeqCst), 1); // Counter unchanged
   }

   // Test initialization failure
   let mut once_err: TOnce<(), String> = TOnce::new(());
   let counter_err = AtomicUsize::new(0);
   let result = once_err
      .get_mut_or_try_init_async(|_p| {
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
         .get_mut_or_try_init_async(|_p| {
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
   let once = TOnce::<(), i32>::with_value(42);
   let clone = once.clone();

   assert_eq!(once.get(), Some(&42));
   assert_eq!(clone.get(), Some(&42));
   assert!(once.is_done());
   assert!(clone.is_done());

   let empty: TOnce<i32, i32> = TOnce::new(77);
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

// ===== Drop behavior tests using Rc =====

#[test]
fn test_drop_param_on_init() {
   // Verify that the parameter is dropped when the cell is initialized
   let param = Arc::new(100u32);
   let param_clone = Arc::clone(&param);

   let once: TOnce<Arc<u32>, String> = TOnce::new(param);
   assert_eq!(Arc::strong_count(&param_clone), 2); // once + param_clone

   // Initialize the cell - this should drop the parameter
   let _value = once.get_or_init(|p| format!("value: {}", *p));
   assert_eq!(once.get(), Some(&String::from("value: 100")));

   // Parameter should have been dropped
   assert_eq!(Arc::strong_count(&param_clone), 1); // only param_clone remains
}

#[test]
fn test_drop_value_on_take() {
   // Verify that the value is dropped when taken
   let value = Arc::new(42u32);
   let value_clone = Arc::clone(&value);

   let mut once = TOnce::<i32, Arc<u32>>::with_value(value);
   assert_eq!(Arc::strong_count(&value_clone), 2); // once + value_clone

   // Take the value out
   let taken = once.take(99);
   assert!(taken.is_ok());
   let taken_value = taken.unwrap();
   assert_eq!(Arc::strong_count(&value_clone), 2); // taken_value + value_clone

   // Drop the taken value
   drop(taken_value);
   assert_eq!(Arc::strong_count(&value_clone), 1); // only value_clone remains
}

#[test]
fn test_drop_value_on_replace() {
   // Verify that the old value is dropped when replaced
   let value1 = Arc::new(1u32);
   let value1_clone = Arc::clone(&value1);
   let value2 = Arc::new(2u32);
   let value2_clone = Arc::clone(&value2);

   let mut once = TOnce::<(), Arc<u32>>::with_value(value1);
   assert_eq!(Arc::strong_count(&value1_clone), 2); // once + value1_clone

   // Replace the value
   let old = once.replace_mut(value2);
   assert!(old.is_some());
   let old_value = old.unwrap();
   assert_eq!(Arc::strong_count(&value1_clone), 2); // old_value + value1_clone
   assert_eq!(Arc::strong_count(&value2_clone), 2); // once + value2_clone

   // Drop the old value
   drop(old_value);
   assert_eq!(Arc::strong_count(&value1_clone), 1); // only value1_clone
   assert_eq!(Arc::strong_count(&value2_clone), 2); // once + value2_clone
}

#[test]
fn test_drop_on_once_drop() {
   // Verify that values are properly dropped when Once is dropped
   let param = Arc::new(10u32);
   let value = Arc::new(20u32);

   {
      let once: TOnce<Arc<u32>, Arc<u32>> = TOnce::new(Arc::clone(&param));
      assert_eq!(Arc::strong_count(&param), 2);

      // Initialize with value
      once.get_or_init(|_p| Arc::clone(&value));
      assert_eq!(Arc::strong_count(&param), 1); // param dropped on init
      assert_eq!(Arc::strong_count(&value), 2); // once + value_clone
   } // once dropped here

   assert_eq!(Arc::strong_count(&param), 1); // only param_clone
   assert_eq!(Arc::strong_count(&value), 1); // only value_clone
}

#[test]
fn test_drop_param_on_set() {
   // Verify parameter is dropped when set() is used
   let param = Arc::new(5u32);
   let param_clone = Arc::clone(&param);
   let value = Arc::new(15u32);
   let value_clone = Arc::clone(&value);

   let once: TOnce<Arc<u32>, Arc<u32>> = TOnce::new(param);
   assert_eq!(Arc::strong_count(&param_clone), 2);

   // Set the value directly
   once.set(value).unwrap();
   assert_eq!(Arc::strong_count(&param_clone), 1); // param dropped
   assert_eq!(Arc::strong_count(&value_clone), 2); // once + value_clone
}

#[test]
fn test_no_double_drop() {
   // Ensure no double-drops occur in edge cases
   let param = Arc::new(1u32);
   let param_clone = Arc::clone(&param);

   let mut once: TOnce<Arc<u32>, String> = TOnce::new(param);
   assert_eq!(Arc::strong_count(&param_clone), 2);

   // Initialize
   once.get_mut_or_init(|p| format!("val: {}", *p));
   assert_eq!(Arc::strong_count(&param_clone), 1); // param dropped

   // Replace multiple times - should not cause issues
   once.replace_mut(String::from("new1"));
   once.replace_mut(String::from("new2"));

   // Take the value
   let _taken = once.take(Arc::new(99u32));

   // Cell is now uninitialized with new param
   // Drop the once - should clean up properly
   drop(once);

   // Original param should still have correct count
   assert_eq!(Arc::strong_count(&param_clone), 1);
}

#[test]
fn test_drop_with_failed_try_init() {
   // Verify parameter is retained when initialization fails
   let param = Arc::new(7u32);
   let param_clone = Arc::clone(&param);

   let once: TOnce<Arc<u32>, String> = TOnce::new(param);
   assert_eq!(Arc::strong_count(&param_clone), 2);

   // Try to initialize but fail
   let result = once.get_or_try_init(|_p| Err::<String, &str>("init failed"));
   assert!(result.is_err());

   // Parameter should still be held by once
   assert_eq!(Arc::strong_count(&param_clone), 2);

   // Now initialize successfully
   let result = once.get_or_try_init(|p| Ok::<_, &str>(format!("success: {}", **p)));
   assert!(result.is_ok());

   // Now parameter should be dropped
   assert_eq!(Arc::strong_count(&param_clone), 1);
}
