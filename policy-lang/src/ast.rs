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
    Map(Box<QueryExpr>, Func),
    FlatMap(Box<QueryExpr>, Func),

    LookupById(String, Box<QueryExpr>),
    Find(String, Vec<(FieldComparison, String, Box<QueryExpr>)>),

    Set(Vec<Box<QueryExpr>>),
    If(Box<QueryExpr>, Box<QueryExpr>, Box<QueryExpr>),
    Match(Box<QueryExpr>, String, Box<QueryExpr>, Box<QueryExpr>),

    DateTimeConst(u32, u32, u32, u32, u32, u32),
    Now,
    Public,
    IntConst(i64),
    FloatConst(f64),
    StringConst(String),
    BoolConst(bool),
    None,
    Some(Box<QueryExpr>),
}
#[derive(Debug, PartialEq, Clone)]
pub struct ObjectLiteral {
    pub coll: String,
    pub fields: Vec<(String, Box<QueryExpr>)>,
    pub template_obj: Option<Box<QueryExpr>>,
}
#[derive(Debug, PartialEq, Clone)]
pub enum FieldComparison {
    Equals,
    Greater,
    GreaterOrEquals,
    Less,
    LessOrEquals,
}
impl fmt::Display for FieldComparison {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FieldComparison::Equals => write!(f, ":"),
            FieldComparison::Greater => write!(f, ">"),
            FieldComparison::GreaterOrEquals => write!(f, ">="),
            FieldComparison::Less => write!(f, "<"),
            FieldComparison::LessOrEquals => write!(f, "<="),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Policy {
    Public,
    None,
    Func(Func),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Func {
    pub param: String,
    pub expr: Box<QueryExpr>,
}

#[derive(Debug, PartialEq)]
pub struct GlobalPolicy {
    pub static_principals: Vec<StaticPrincipal>,
    pub collections: Vec<CollectionPolicy>,
}

#[derive(Debug, PartialEq)]
pub struct StaticPrincipal {
    pub name: String,
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
    Principal,
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
    DateTime,
    Id(String),
    Set(Box<FieldType>),
    Option(Box<FieldType>),
}

impl fmt::Display for FieldType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FieldType::String => write!(f, "String"),
            FieldType::I64 => write!(f, "i64"),
            FieldType::F64 => write!(f, "f64"),
            FieldType::DateTime => write!(f, "DateTime"),
            FieldType::Id(coll) => write!(f, "Id({})", coll),
            FieldType::Bool => write!(f, "bool"),
            FieldType::Set(inner_type) => write!(f, "Set({})", inner_type),
            FieldType::Option(inner_type) => write!(f, "Option({})", inner_type),
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
        collections: Vec<CollectionPolicy>,
    },
    Delete {
        table_name: String,
    },
    ObjectCommand(ObjectCommand),

    AddStaticPrincipal {
        name: String,
    },
    AddPrincipal {
        table_name: String,
    },
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
        pol: FieldPolicy,
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
        kind: FieldPolicyKind,
        pol: Policy,
    },
    TightenFieldPolicy {
        field: String,
        kind: FieldPolicyKind,
        pol: Policy,
    },
    LoosenCollectionPolicy {
        kind: CollectionPolicyKind,
        pol: Policy,
    },
    TightenCollectionPolicy {
        kind: CollectionPolicyKind,
        pol: Policy,
    },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum FieldPolicyKind {
    Edit,
    Read,
}

impl fmt::Display for FieldPolicyKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FieldPolicyKind::Edit => write!(f, "edit"),
            FieldPolicyKind::Read => write!(f, "read"),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum CollectionPolicyKind {
    Create,
    Delete,
}
