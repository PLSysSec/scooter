use std::collections::HashMap;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum QueryExpr {
    Path(Vec<String>),
    Plus(Box<QueryExpr>, Box<QueryExpr>),
    IntConst(i64),
    FloatConst(f64),
    StringConst(String),
    Object(ObjectLiteral),
}
#[derive(Debug, PartialEq)]
pub struct ObjectLiteral {
    pub coll: String,
    pub fields: Vec<(String, Box<QueryExpr>)>,
    pub template_obj: Option<Box<QueryExpr>>,
}

#[derive(Debug, PartialEq)]
pub enum Policy {
    Public,
    None,
    Func(Func),
}

#[derive(Debug, PartialEq)]
pub struct Func {
    pub param: String,
    pub expr: Box<QueryExpr>,
}

#[derive(Debug, PartialEq)]
pub struct GlobalPolicy {
    pub collections: Vec<CollectionPolicy>,
}

#[derive(Debug, PartialEq)]
pub struct CollectionPolicy {
    pub name: String,
    pub create: Policy,
    pub delete: Policy,
    pub fields: HashMap<String, FieldPolicy>,
}

#[derive(Debug, PartialEq)]
pub struct FieldPolicy {
    pub ty: FieldType,
    pub read: Policy,
    pub write: Policy,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FieldType {
    String,
    I64,
    F64,
    Id(String),
}

impl fmt::Display for FieldType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FieldType::String => write!(f, "String"),
            FieldType::I64 => write!(f, "i64"),
            FieldType::F64 => write!(f, "f64"),
            FieldType::Id(coll) => write!(f, "Id({})", coll),
        }
    }
}

// Migration Lang stuff

#[derive(Debug, PartialEq)]
pub struct Migration(pub Vec<MigrationCommand>);

#[derive(Debug, PartialEq)]
pub enum MigrationCommand {
    CollAction {
        table: String,
        action: MigrationAction,
    },
    Create{table_name: String, layout: Vec<(String, FieldType)>},
    Delete{table_name: String},
}

#[derive(Debug, PartialEq)]
pub enum ObjectCommand {
    CreateObject{collection: String, value: Box<QueryExpr>},
    DeleteObject{collection: String, id_expr: Box<QueryExpr>},
}

#[derive(Debug, PartialEq)]
pub enum MigrationAction {
    RemoveField{field: String},
    AddField{field: String, ty: FieldType, init: Func},
    ChangeField{field: String, new_ty: FieldType, new_init: Func},
    RenameField{old_field: String, new_field: String},
    ForEach{param: String, body: ObjectCommand},
}
