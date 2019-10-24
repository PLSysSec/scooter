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

pub struct CheckedCollection <'a> {
    name : &'a str,
    inner_coll : Collection,
}

use mongodb::Document;
use mongodb::coll::Collection;
use mongodb::coll::results::InsertManyResult;
use mongodb::db::ThreadedDatabase;
use mongodb::Client;
use mongodb::ThreadedClient;

impl CheckedCollection <'_> {
    pub fn new(db_name : &str) -> CheckedCollection {
        let client = Client::connect("localhost", 27017)
            .expect("Failed to initialize client.");
        let db = client.db(db_name);
        db.create_collection("User", None)
            .expect("Failed to create collection");
        CheckedCollection {name:db_name.clone(), inner_coll: db.collection("User")}
    }
    pub fn insert_many(&self, items : Vec<Document>) -> Option<Vec<RecordId>> {
        match self.inner_coll.insert_many(items, None) {
            Result::Ok(InsertManyResult{inserted_ids: ids, ..}) =>
                Some(ids.unwrap().values().map(|b| b.as_object_id().unwrap().clone()).collect()),
            _ => None
        }
    }
    pub fn find_one(&self, filter : Document) -> Option<Document>{
        match self.inner_coll.find_one(Some(filter), None) {
            Result::Ok(Some(doc)) => Some(doc),
            _ => None
        }
    }
}
impl Drop for CheckedCollection <'_>{
    fn drop(&mut self) {
        let client = Client::connect("localhost", 27017)
            .expect("Failed to initialize client.");
        let db = client.db(self.name);
        db.drop_collection("User")
            .expect("Failed to drop collection!");
    }
}
