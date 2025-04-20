use std::sync::atomic::{AtomicUsize, Ordering};

use poly_once::Once;

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
   let threads: Vec<_> = (0..5)
      .map(|_| {
         std::thread::spawn(|| {
            println!("Thread access: {}", get_data());
         })
      })
      .collect();

   for t in threads {
      t.join().unwrap();
   }

   assert_eq!(DATA.get(), Some(&"Expensive data".to_string()));
   assert_eq!(COUNTER.load(Ordering::Relaxed), 1); // Initializer ran only once
   println!("Final data: {}", get_data());
}
