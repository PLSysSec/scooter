pub mod migrate;
#[cfg(not(feature = "naive-smt"))]
pub mod smt;

#[cfg(feature = "naive-smt")]
pub mod smt2;
#[cfg(feature = "naive-smt")]
pub use smt2 as smt;
