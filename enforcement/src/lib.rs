pub use enforcement_macros::collection;
use mongodb::oid::ObjectId;
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
use mongodb::coll::Collection;
use mongodb::coll::results::InsertManyResult;
use mongodb::db::ThreadedDatabase;
use mongodb::Client;
use mongodb::ThreadedClient;
use std::marker::PhantomData;

pub struct CheckedCollection <'a, T: MongoDocument> {
    name : &'a str,
    inner_coll : Collection,
    element_type : PhantomData<T>,
}

impl <T: MongoDocument> CheckedCollection <'_, T> {
    pub fn new(db_name : &str) -> CheckedCollection <T> {
        let client = Client::connect("localhost", 27017)
            .expect("Failed to initialize client.");
        let db = client.db(db_name);
        db.create_collection("User", None)
            .expect("Failed to create collection");
        CheckedCollection {name:db_name.clone(), inner_coll: db.collection("User"),
                           element_type:PhantomData}
    }
    pub fn insert_many(&self, items : Vec<T>) -> Option<Vec<RecordId>> {
        match self.inner_coll.insert_many(items.iter()
                                          .map(T::to_document).collect(), None) {
            Result::Ok(InsertManyResult{inserted_ids: ids, ..}) =>
                Some(ids.unwrap().values().map(|b| b.as_object_id().unwrap().clone()).collect()),
            _ => None
        }
    }
    pub fn find_by_id(&self, id : RecordId) -> Option<T> {
        match self.inner_coll.find_one(Some(doc! {"_id":id}), None) {
            Result::Ok(Some(doc)) => Some(T::from_document(doc)),
            _ => None
        }
    }
}
impl<T> Drop for CheckedCollection <'_, T> where T : MongoDocument{
    fn drop(&mut self) {
        let client = Client::connect("localhost", 27017)
            .expect("Failed to initialize client.");
        let db = client.db(self.name);
        db.drop_collection("User")
            .expect("Failed to drop collection!");
    }
}
