pub mod migrate;
#[cfg(not(feature = "naive-smt"))]
pub mod smt;

#[cfg(feature = "naive-smt")]
pub mod naive_smt;
#[cfg(feature = "naive-smt")]
pub use naive_smt as smt;
