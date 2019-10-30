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
use mongodb::db::Database;
use mongodb::Client;
use mongodb::ThreadedClient;

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
