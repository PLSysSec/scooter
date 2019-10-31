use std::collections::HashMap;
use std::hash::Hash;

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
    pub fields: HashMap<ID, FieldPolicy<ID>>
}

#[derive(Debug, PartialEq, Eq)]
pub struct FieldPolicy<ID> {
    pub read: Policy<ID>,
    pub write: Policy<ID>
}


