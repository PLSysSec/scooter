use std::collections::HashMap;
use std::fmt;

#[derive(Debug, PartialEq, Eq)]
pub enum QueryExpr {
    Path(Vec<String>),
    Or(Box<QueryExpr>, Box<QueryExpr>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Policy {
    Public,
    None,
    Func(PolicyFunc),
}

#[derive(Debug, PartialEq, Eq)]
pub struct PolicyFunc {
    pub param: String,
    pub expr: Box<QueryExpr>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct GlobalPolicy {
    pub collections: Vec<CollectionPolicy>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct CollectionPolicy {
    pub name: String,
    pub create: Policy,
    pub delete: Policy,
    pub fields: HashMap<String, FieldPolicy>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct FieldPolicy {
    pub ty: FieldType,
    pub read: Policy,
    pub write: Policy,
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
