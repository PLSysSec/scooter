use std::collections::HashMap;
use std::hash::Hash;
use std::fmt;

#[derive(Debug, PartialEq, Eq)]
pub enum QueryExpr<ID> {
    Path(Vec<ID>),
    Or(Box<QueryExpr<ID>>, Box<QueryExpr<ID>>)
}


#[derive(Debug, PartialEq, Eq)]
pub enum Policy<ID> {
    Public,
    None,
    Func(PolicyFunc<ID>)
}

#[derive(Debug, PartialEq, Eq)]
pub struct PolicyFunc<ID> {
    pub param: ID,
    pub expr: Box<QueryExpr<ID>>
}

#[derive(Debug, PartialEq, Eq)]
pub struct GlobalPolicy<ID: Hash + Eq> {
    pub collections: Vec<CollectionPolicy<ID>>
}

#[derive(Debug, PartialEq, Eq)]
pub struct CollectionPolicy<ID: Hash + Eq> {
    pub name: ID,
    pub create: Policy<ID>,
    pub delete: Policy<ID>,
    pub fields: HashMap<ID, FieldPolicy<ID>>
}

#[derive(Debug, PartialEq, Eq)]
pub struct FieldPolicy<ID> {
    pub ty: FieldType,
    pub read: Policy<ID>,
    pub write: Policy<ID>
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FieldType {
    String,
    I64,
    I32,
    F64,
    RecordId,
}

impl fmt::Display for FieldType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FieldType::String => write!(f, "String"),
            FieldType::I64 => write!(f, "i64"),
            FieldType::I32 => write!(f, "i32"),
            FieldType::F64 => write!(f, "f64"),
            FieldType::RecordId => write!(f, "RecordId"),
        }
    }
}
