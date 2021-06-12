pub use id_arena::Id;

use std::{
    error::Error,
    fmt::{self, Display},
    hash::Hash,
    marker::PhantomData,
};

macro_rules! type_error {
    ( $($body:expr),+ ) => { { return Err(Box::new(crate::ir::TypeError::new(format!($($body),*)))); } }
}

pub mod expr;
pub mod migration;
pub mod policy;
pub mod schema;

/// Idents represent any identifier across the policy languages.
/// This includes variables, collections, field names, etc.
/// They consist of the original name and a unique index,
/// and are created during lowering.
#[derive(Debug, Clone)]
pub struct Ident<T> {
    pub index: u32,
    pub orig_name: String,
    pd: PhantomData<T>,
}

impl<T> Ident<T> {
    pub fn new(s: impl ToString) -> Self {
        static mut IDENT_CT: u32 = 0;
        let index = unsafe {
            IDENT_CT += 1;
            IDENT_CT
        };
        Ident {
            index,
            orig_name: s.to_string(),
            pd: PhantomData::default(),
        }
    }

    pub fn coerce<U>(&self) -> Ident<U> {
        Ident::<U> {
            index: self.index,
            orig_name: self.orig_name.clone(),
            pd: PhantomData::default(),
        }
    }
    pub fn unsafe_construct(index: u32, orig_name: String) -> Self {
        Self {
            index,
            orig_name,
            pd: PhantomData::default(),
        }
    }

    fn eq_str(&self, s: impl AsRef<str>) -> bool {
        self.orig_name == s.as_ref()
    }
}

impl<T> Hash for Ident<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

impl<T> PartialEq for Ident<T> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}
impl<T> Eq for Ident<T> {}

#[derive(Debug)]
pub struct TypeError {
    msg: String,
}

impl TypeError {
    fn new(s: impl ToString) -> Self {
        Self { msg: s.to_string() }
    }
}

impl Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.msg)
    }
}

impl Error for TypeError {}
