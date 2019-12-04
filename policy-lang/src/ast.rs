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
    Id(String),
}

impl fmt::Display for FieldType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FieldType::String => write!(f, "String"),
            FieldType::I64 => write!(f, "i64"),
            FieldType::I32 => write!(f, "i32"),
            FieldType::F64 => write!(f, "f64"),
            FieldType::Id(coll) => write!(f, "Id({})", coll),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct MigrationCommandList(pub Vec<MigrationCommand>);

#[derive(Debug, PartialEq, Eq)]
pub struct MigrationCommand {
    pub table: String,
    pub action: MigrationAction,
}

#[derive(Debug, PartialEq, Eq)]
pub enum MigrationAction {
    RemoveColumn{col: String}
}
