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
   assert_eq!(
      MAYBE_DATA.get(),
      Some(&"Successfully initialized".to_string())
   );

   // Subsequent attempts (even failing ones) return the initialized value
   match try_get_data(true) {
      Ok(data) => println!("Got data again: {}", data),
      Err(_) => panic!("Should have returned existing data"),
   }
}
