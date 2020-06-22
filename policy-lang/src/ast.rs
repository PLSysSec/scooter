use std::fmt;

#[derive(Debug, PartialEq, Clone)]
pub enum QueryExpr {
    Plus(Box<QueryExpr>, Box<QueryExpr>),
    Minus(Box<QueryExpr>, Box<QueryExpr>),

    IsEq(Box<QueryExpr>, Box<QueryExpr>),
    IsNeq(Box<QueryExpr>, Box<QueryExpr>),
    Not(Box<QueryExpr>),

    IsLess(Box<QueryExpr>, Box<QueryExpr>),
    IsLessOrEq(Box<QueryExpr>, Box<QueryExpr>),
    IsGreater(Box<QueryExpr>, Box<QueryExpr>),
    IsGreaterOrEq(Box<QueryExpr>, Box<QueryExpr>),

    Var(String),
    FieldAccess(Box<QueryExpr>, String),
    Object(ObjectLiteral),

    LookupById(String, Box<QueryExpr>),
    Find(String, Vec<(String, Box<QueryExpr>)>),

    List(Vec<Box<QueryExpr>>),
    If(Box<QueryExpr>, Box<QueryExpr>, Box<QueryExpr>),

    IntConst(i64),
    FloatConst(f64),
    StringConst(String),
    BoolConst(bool),
}
#[derive(Debug, PartialEq, Clone)]
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
    pub fields: Vec<(String, FieldPolicy)>,
    pub annotations: Vec<Annotation>,
}

#[derive(Debug, PartialEq)]
pub enum Annotation {
    Principle,
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
    Bool,
    Id(String),
    List(Box<FieldType>),
}

impl fmt::Display for FieldType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FieldType::String => write!(f, "String"),
            FieldType::I64 => write!(f, "i64"),
            FieldType::F64 => write!(f, "f64"),
            FieldType::Id(coll) => write!(f, "Id({})", coll),
            FieldType::Bool => write!(f, "bool"),
            FieldType::List(inner_type) => write!(f, "[{}]", inner_type),
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
    Create {
        collection: CollectionPolicy,
    },
    Delete {
        table_name: String,
    },
    ObjectCommand(ObjectCommand),
}

#[derive(Debug, PartialEq)]
pub enum ObjectCommand {
    ForEach {
        collection: String,
        param: String,
        body: Box<ObjectCommand>,
    },
    CreateObject {
        collection: String,
        value: Box<QueryExpr>,
    },
    DeleteObject {
        collection: String,
        id_expr: Box<QueryExpr>,
    },
}

#[derive(Debug, PartialEq)]
pub enum MigrationAction {
    RemoveField {
        field: String,
    },
    AddField {
        field: String,
        ty: FieldType,
        init: Func,
    },
    ChangeField {
        field: String,
        new_ty: FieldType,
        new_init: Func,
    },
    RenameField {
        old_field: String,
        new_field: String,
    },
    LoosenFieldPolicy {
        field: String,
        kind: String,
        pol: Policy,
    },
    TightenFieldPolicy {
        field: String,
        kind: String,
        pol: Policy,
    },
    LoosenCollectionPolicy {
        kind: String,
        pol: Policy,
    },
    TightenCollectionPolicy {
        kind: String,
        pol: Policy,
    },
}
