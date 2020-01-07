pub use enforcement_macros::collection;
use mongodb::oid::ObjectId;
pub use mongodb::{bson, doc};
mod from_bson;
pub use from_bson::*;
use serde::{Serialize, Deserialize, Serializer, Deserializer};
pub mod translate;
use std::marker::PhantomData;
use std::fmt;


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
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct RecordId(ObjectId);
impl RecordId {
    pub fn from_object_id(id: ObjectId) -> RecordId {
        RecordId(id)
    }
}

pub struct TypedRecordId<T: DBCollection>(RecordId,
                                          PhantomData<T>);

impl <T> Serialize for TypedRecordId<T> where T: DBCollection {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer {
        self.0.serialize(serializer)
    }
}
impl <'de, T> Deserialize<'de> for TypedRecordId<T> where T: DBCollection {
    fn deserialize<D>(deserializer: D) -> Result<TypedRecordId<T>, D::Error>
    where
        D: Deserializer<'de> {
        Ok(Self(RecordId::deserialize(deserializer)?, PhantomData))
    }
}
impl <T> Clone for TypedRecordId<T> where T: DBCollection {
    fn clone(&self) -> Self {
        TypedRecordId(self.0.clone(), PhantomData)
    }
}

impl <T> PartialEq for TypedRecordId<T> where T: DBCollection {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl <T> Eq for TypedRecordId<T> where T: DBCollection {
}

impl <T> fmt::Debug for TypedRecordId<T> where T: DBCollection {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypedRecordId({:?})", self.0)
    }
}

impl <T> TypedRecordId<T> where T: DBCollection{
    pub fn lookup(&self, conn: &AuthConn) -> Option<T> {
        T::find_full_by_id(conn.conn(), self.clone().into())
    }
}

impl <T> From<TypedRecordId<T>> for RecordId  where T: DBCollection{
    fn from(id: TypedRecordId<T>) -> RecordId {
        id.0
    }
}

pub trait ToRecordIdVec {
    fn to_record_id_vec(&self) -> Vec<RecordId>;
}
impl ToRecordIdVec for RecordId {
    fn to_record_id_vec(&self) -> Vec<RecordId>{
        vec![self.clone()]
    }
}
impl ToRecordIdVec for Option<RecordId> {
    fn to_record_id_vec(&self) -> Vec<RecordId>{
        vec![self.clone().unwrap()]
    }
}

impl<T> ToRecordIdVec for TypedRecordId<T> where T: DBCollection{
    fn to_record_id_vec(&self) -> Vec<RecordId>{
        vec![self.clone().into()]
    }
}

impl<T> ToRecordIdVec for Vec<TypedRecordId<T>> where T: DBCollection {
    fn to_record_id_vec(&self) -> Vec<RecordId>{
        self.iter().map(|v| v.clone().into()).collect()
    }
}

impl From<RecordId> for ObjectId {
    fn from(id: RecordId) -> ObjectId {
        id.0
    }
}
impl From<ObjectId> for RecordId {
    fn from(id: ObjectId) -> RecordId {
        RecordId(id)
    }
}
impl <T> From<ObjectId> for TypedRecordId<T> where T: DBCollection {
    fn from(id: ObjectId) -> TypedRecordId<T> {
        TypedRecordId(RecordId(id), PhantomData)
    }
}
impl From<RecordId> for mongodb::Bson {
    fn from(id: RecordId) -> mongodb::Bson {
        id.0.into()
    }
}
impl<T> From<TypedRecordId<T>> for mongodb::Bson where T: DBCollection{
    fn from(id: TypedRecordId<T>) -> mongodb::Bson {
        id.0.into()
    }
}
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
    type Partial;
    fn find_by_id(connection: &AuthConn, id: RecordId) -> Option<Self::Partial>;
    fn find_full_by_id(connection: &DBConn, id: RecordId) -> Option<Self>;
    fn insert_one(connection: &AuthConn, item: Self) -> Option<TypedRecordId<Self>>;
    fn insert_many(connection: &AuthConn, items: Vec<Self>) -> Option<Vec<TypedRecordId<Self>>>;
    fn save_all(connection: &AuthConn, items: Vec<&Self::Partial>) -> bool;
    fn delete_by_id(connection: &AuthConn, id: RecordId) -> bool;
}
