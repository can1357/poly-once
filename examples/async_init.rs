use std::sync::atomic::{AtomicUsize, Ordering};

use poly_once::Once;
use tokio::time::{sleep, Duration};

static COUNTER: AtomicUsize = AtomicUsize::new(0);
static ASYNC_DATA: Once<String> = Once::new();

async fn get_async_data() -> &'static String {
   ASYNC_DATA
      .get_or_init_async(|| async {
         // This async block runs only once
         COUNTER.fetch_add(1, Ordering::Relaxed);
         println!("Initializing async data...");
         sleep(Duration::from_millis(50)).await;
         "Async expensive data".to_string()
      })
      .await
}

#[tokio::main]
async fn main() {
   let tasks: Vec<_> = (0..5)
      .map(|_| {
         tokio::spawn(async {
            println!("Task access: {}", get_async_data().await);
         })
      })
      .collect();

   for t in tasks {
      t.await.unwrap();
   }

   assert_eq!(ASYNC_DATA.get(), Some(&"Async expensive data".to_string()));
   assert_eq!(COUNTER.load(Ordering::Relaxed), 1); // Initializer ran only once
   println!("Final async data: {}", get_async_data().await);
}
