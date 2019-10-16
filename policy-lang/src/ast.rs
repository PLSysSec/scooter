use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq)]
pub enum QueryExpr {
    Path(Vec<String>),
    Or(Box<QueryExpr>, Box<QueryExpr>)
}


#[derive(Debug, PartialEq, Eq)]
pub enum Policy {
    Public,
    None,
    Func(PolicyFunc)
}

#[derive(Debug, PartialEq, Eq)]
pub struct PolicyFunc {
    pub param: String,
    pub expr: Box<QueryExpr>
}

#[derive(Debug, PartialEq, Eq)]
pub struct GlobalPolicy {
    pub collections: Vec<CollectionPolicy>
}

#[derive(Debug, PartialEq, Eq)]
pub struct CollectionPolicy {
    pub name: String,
    pub fields: HashMap<String, FieldPolicy>
}

#[derive(Debug, PartialEq, Eq)]
pub struct FieldPolicy {
    pub read: Policy,
    pub write: Policy
}


