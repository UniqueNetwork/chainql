#![allow(unused_imports)]

#[cfg(all(feature = "log", feature = "log-tracing"))]
compile_error!("Features `log-tracing` and `log` cannot be enabled together");

#[cfg(all(not(feature = "log"), not(feature = "log-tracing")))]
compile_error!("You should enable `log-tracing` or `log` feature");

#[cfg(all(feature = "log-tracing", not(feature = "log")))]
pub use tracing::{debug, info, warn, error};

#[cfg(all(feature = "log", not(feature = "log-tracing")))]
pub use log::{debug, info, warn, error};