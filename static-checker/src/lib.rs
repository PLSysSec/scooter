pub mod migrate;
#[cfg(not(feature = "naive_smt"))]
pub mod smt;

#[cfg(feature = "naive_smt")]
pub mod smt2;
#[cfg(feature = "naive_smt")]
pub use smt2 as smt;
