pub use enforcement_macros::collection;
use mongodb::oid::ObjectId;
pub use mongodb::{bson, doc};
mod from_bson;
pub use from_bson::*;


#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Principle {
    Id(RecordId),
    Public,
}

#[derive(Debug)]
pub enum PolicyValue {
    Public,
    Ids(Vec<RecordId>),
}
impl PolicyValue {
    pub fn accessible_by(&self, user: &Principle) -> bool {
        match (self, user) {
            (Self::Public, _) => true,
            (Self::Ids(ids), Principle::Id(user)) => ids.iter().find(|&el| *el == *user).is_some(),
            _ => false
        }
    }
}

pub trait MongoDocument {
    fn from_document(doc: mongodb::Document) -> Self;
    fn to_document(&self) -> mongodb::Document;
}
pub type RecordId = ObjectId;
use mongodb::coll::results::InsertManyResult;
use mongodb::coll::Collection;
use mongodb::db::Database;
use mongodb::db::ThreadedDatabase;
use mongodb::Client;
use mongodb::ThreadedClient;
use std::marker::PhantomData;

pub struct DBConn {
    pub mongo_conn: Database,
}

impl DBConn {
    pub fn as_princ(&self, id: Principle) -> AuthConn {
        AuthConn {
            inner_conn: self,
            principle: id,
        }
    }
    pub fn new(db_name: &str) -> DBConn {
        let client = Client::connect("localhost", 27017)
            .expect("Failed to initialize client.");
        DBConn {mongo_conn: client.db(db_name)}
    }
}

pub struct AuthConn<'a> {
    inner_conn: &'a DBConn,
    principle: Principle,
}

impl <'a> AuthConn <'a>{
    pub fn conn(&self) -> &'a DBConn {
        self.inner_conn
    }
    pub fn principle(&self) -> Principle {
        self.principle.clone()
    }
}

pub trait DBCollection: Sized {
    fn find_by_id(connection: AuthConn, id: RecordId) -> Option<Self>;
    fn insert_many(connection: AuthConn, items: Vec<Self>) -> Option<Vec<RecordId>>;
}

pub struct CheckedCollection<'a, T: MongoDocument> {
    name: &'a str,
    inner_coll: Collection,
    element_type: PhantomData<T>,
}

impl<T: MongoDocument> CheckedCollection<'_, T> {
    pub fn new(db_name: &str) -> CheckedCollection<T> {
        let client = Client::connect("localhost", 27017).expect("Failed to initialize client.");
        let db = client.db(db_name);
        db.create_collection("User", None)
            .expect("Failed to create collection");
        CheckedCollection {
            name: db_name.clone(),
            inner_coll: db.collection("User"),
            element_type: PhantomData,
        }
    }
    pub fn insert_many(&self, items: Vec<T>) -> Option<Vec<RecordId>> {
        match self
            .inner_coll
            .insert_many(items.iter().map(T::to_document).collect(), None)
        {
            Result::Ok(InsertManyResult {
                inserted_ids: ids, ..
            }) => Some(
                ids.unwrap()
                    .values()
                    .map(|b| b.as_object_id().unwrap().clone())
                    .collect(),
            ),
            _ => None,
        }
    }
    pub fn find_by_id(&self, id: RecordId) -> Option<T> {
        match self.inner_coll.find_one(Some(doc! {"_id":id}), None) {
            Result::Ok(Some(doc)) => Some(T::from_document(doc)),
            _ => None,
        }
    }
}
impl<T> Drop for CheckedCollection<'_, T>
where
    T: MongoDocument,
{
    fn drop(&mut self) {
        let client = Client::connect("localhost", 27017).expect("Failed to initialize client.");
        let db = client.db(self.name);
        db.drop_collection("User")
            .expect("Failed to drop collection!");
    }
}
