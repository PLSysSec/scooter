use mongodb::oid::ObjectId;
pub use enforcement_macros::collection;
pub use mongodb::{bson, doc};
mod from_bson;
pub use from_bson::*;

pub type PrincipleId = ObjectId;

#[derive(Debug)]
pub enum PolicyValue {
    Public,
    Ids(Vec<PrincipleId>),
}
impl PolicyValue {
    pub fn accessible_by(&self, user: &PrincipleId) -> bool {
        match self {
            Self::Public => true,
            Self::Ids(ids) => ids.iter().find(|&el| *el == *user).is_some(),
        }
    }
}

pub trait MongoDocument {
    fn from_document(doc: mongodb::Document) -> Self;
    fn to_document(&self) -> mongodb::Document;
}
pub type RecordId = ObjectId;
