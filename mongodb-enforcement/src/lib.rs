use bson::oid::ObjectId;
use bson::{doc, Bson, Document};
pub use enforcement_macros::collection;
use mongodb::{
    options::{ClientOptions, StreamAddress},
    Client, Database,
};
mod from_bson;
pub use from_bson::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
pub mod translate;
use chrono;
use chrono::TimeZone;
use std::fmt;
use std::fs::read_to_string;
use std::marker::PhantomData;
use std::ops::{Add, Sub};
use std::path::Path;

pub mod gen_prelude {
    pub use ::bson::{self, bson, doc};
    pub use chrono::Utc;
    pub use mongodb;
    pub use serde::Serialize;
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum Principal {
    Id(RecordId),
    Static(&'static str),
    Unauthenticated,
}

#[derive(Debug)]
pub enum PolicyValue {
    Public,
    Set(Vec<Principal>),
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum POption<T> {
    Some(T),
    None,
}

impl From<Vec<RecordId>> for PolicyValue {
    fn from(ids: Vec<RecordId>) -> PolicyValue {
        PolicyValue::Set(ids.into_iter().map(Principal::Id).collect())
    }
}
impl From<Vec<Principal>> for PolicyValue {
    fn from(princs: Vec<Principal>) -> PolicyValue {
        PolicyValue::Set(princs)
    }
}
impl<T> From<Vec<TypedRecordId<T>>> for PolicyValue
where
    T: DBCollection,
{
    fn from(ids: Vec<TypedRecordId<T>>) -> PolicyValue {
        PolicyValue::Set(
            ids.into_iter()
                .map(|v| Principal::Id(v.clone().into()))
                .collect(),
        )
    }
}
impl<T> From<Vec<Option<TypedRecordId<T>>>> for PolicyValue
where
    T: DBCollection,
{
    fn from(ids: Vec<Option<TypedRecordId<T>>>) -> PolicyValue {
        PolicyValue::Set(
            ids.iter()
                .map(|v| Principal::Id(v.clone().unwrap().into()))
                .collect(),
        )
    }
}

impl PolicyValue {
    pub fn accessible_by(&self, user: &Principal) -> bool {
        match (self, user) {
            (Self::Public, _) => true,
            (Self::Set(ids), user) => ids.iter().find(|&el| el == user).is_some(),
        }
    }
}
mod my_date_format {
    use bson::Bson;
    use chrono::offset::Utc;
    use chrono::DateTime;
    use serde::ser::Serialize;
    use serde::Deserialize;
    use serde::Deserializer;
    use serde::Serializer;

    pub fn serialize<S>(datetime: &DateTime<Utc>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let bson = Bson::UtcDatetime(datetime.to_owned());
        bson.serialize(serializer)
    }
    pub fn deserialize<'de, D>(deserializer: D) -> Result<DateTime<Utc>, D::Error>
    where
        D: Deserializer<'de>,
    {
        match Bson::deserialize(deserializer)? {
            Bson::UtcDatetime(datetime) => Ok(datetime),
            _ => panic!("Only Support chrono's DateTime<UTC>."),
        }
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Serialize, Clone, Deserialize, Debug)]
pub struct DateTime(#[serde(with = "my_date_format")] chrono::DateTime<chrono::Utc>);

impl DateTime {
    pub fn now() -> Self {
        DateTime(chrono::Utc::now())
    }
    pub fn to_string(&self) -> String {
        self.0.to_rfc3339()
    }
}
impl Add for DateTime {
    type Output = DateTime;

    fn add(self, other: DateTime) -> DateTime {
        DateTime(self.0 + (chrono::Utc.ymd(0, 0, 0).and_hms(0, 0, 0) - other.0))
    }
}
impl Sub for DateTime {
    type Output = DateTime;

    fn sub(self, other: DateTime) -> DateTime {
        DateTime(self.0 - (chrono::Utc.ymd(0, 0, 0).and_hms(0, 0, 0) - other.0))
    }
}

impl From<DateTime> for Bson {
    fn from(datetime: DateTime) -> Bson {
        Bson::UtcDatetime(datetime.0.to_owned())
    }
}

pub trait MongoDocument {
    fn from_document(doc: Document) -> Self;
    fn to_document(&self) -> Document;
}
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct RecordId(ObjectId);
impl RecordId {
    pub fn from_object_id(id: ObjectId) -> RecordId {
        RecordId(id)
    }

    pub unsafe fn ascribe_collection<T: DBCollection>(self) -> TypedRecordId<T> {
        TypedRecordId(self, PhantomData)
    }
}

pub struct TypedRecordId<T: DBCollection>(RecordId, PhantomData<T>);

impl<T> Serialize for TypedRecordId<T>
where
    T: DBCollection,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}
impl<'de, T> Deserialize<'de> for TypedRecordId<T>
where
    T: DBCollection,
{
    fn deserialize<D>(deserializer: D) -> Result<TypedRecordId<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(Self(RecordId::deserialize(deserializer)?, PhantomData))
    }
}
impl<T> Clone for TypedRecordId<T>
where
    T: DBCollection,
{
    fn clone(&self) -> Self {
        TypedRecordId(self.0.clone(), PhantomData)
    }
}

impl<T> PartialEq for TypedRecordId<T>
where
    T: DBCollection,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for TypedRecordId<T> where T: DBCollection {}

impl<T> fmt::Debug for TypedRecordId<T>
where
    T: DBCollection,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypedRecordId({:?})", self.0)
    }
}

impl<T> TypedRecordId<T>
where
    T: DBCollection,
{
    pub fn lookup(&self, conn: &AuthConn) -> Option<T> {
        T::find_full_by_id(conn.conn(), self.clone().into())
    }
}

impl<T> From<TypedRecordId<T>> for RecordId
where
    T: DBCollection,
{
    fn from(id: TypedRecordId<T>) -> RecordId {
        id.0
    }
}

pub trait ToRecordIdVec {
    fn to_record_id_vec(&self) -> Vec<RecordId>;
}

impl<T> ToRecordIdVec for Vec<Option<TypedRecordId<T>>>
where
    T: DBCollection,
{
    fn to_record_id_vec(&self) -> Vec<RecordId> {
        self.iter().map(|id| id.clone().unwrap().into()).collect()
    }
}

impl<T> ToRecordIdVec for Vec<TypedRecordId<T>>
where
    T: DBCollection,
{
    fn to_record_id_vec(&self) -> Vec<RecordId> {
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
impl<T> From<ObjectId> for TypedRecordId<T>
where
    T: DBCollection,
{
    fn from(id: ObjectId) -> TypedRecordId<T> {
        TypedRecordId(RecordId(id), PhantomData)
    }
}
impl From<RecordId> for Bson {
    fn from(id: RecordId) -> Bson {
        id.0.into()
    }
}
impl<T> From<TypedRecordId<T>> for Bson
where
    T: DBCollection,
{
    fn from(id: TypedRecordId<T>) -> Bson {
        id.0.into()
    }
}
impl<T> From<POption<T>> for Bson
where
    T: Into<Bson>,
{
    fn from(optional_val: POption<T>) -> Bson {
        match optional_val {
            POption::Some(val) => Bson::Document(doc! {"Some": val.into()}),
            POption::None => Bson::String("None".to_string()),
        }
    }
}

#[derive(Clone)]
pub struct DBConn {
    pub mongo_conn: Database,
}

#[derive(Deserialize)]
struct ConnConf {
    host: String,
    port: u16,
    db: String,
}

impl DBConn {
    pub fn as_princ(self, id: Principal) -> AuthConn {
        AuthConn {
            inner_conn: self,
            principal: id,
        }
    }
    pub fn new(host: &str, port: u16, db_name: &str) -> DBConn {
        let options = ClientOptions::builder()
            .hosts(vec![StreamAddress {
                hostname: host.into(),
                port: Some(port),
            }])
            .build();

        let client = Client::with_options(options).expect("Failed to initialize client.");
        DBConn {
            mongo_conn: client.database(db_name),
        }
    }

    pub fn from_toml_conf<P: AsRef<Path>>(conf: P) -> DBConn {
        let conf: ConnConf = toml::from_str(&read_to_string(conf).unwrap()).unwrap();
        Self::new(&conf.host, conf.port, &conf.db)
    }
}

pub struct AuthConn {
    inner_conn: DBConn,
    principal: Principal,
}

impl AuthConn {
    pub fn conn(&self) -> &DBConn {
        &self.inner_conn
    }
    pub fn principal(&self) -> Principal {
        self.principal.clone()
    }
}

pub trait DBCollection: Sized {
    type Partial;
    type Query;
    fn find_by_id(connection: &AuthConn, id: TypedRecordId<Self>) -> Option<Self::Partial>;
    fn find_all(connection: &AuthConn) -> Option<Vec<Self::Partial>>;
    fn find_full_by_id(connection: &DBConn, id: TypedRecordId<Self>) -> Option<Self>;
    fn find_full_by_template(connection: &AuthConn, template: Self::Query) -> Option<Vec<Self>>;
    fn insert_one(connection: &AuthConn, item: Self) -> Option<TypedRecordId<Self>>;
    fn insert_many(connection: &AuthConn, items: Vec<Self>) -> Option<Vec<TypedRecordId<Self>>>;
    fn save_all(connection: &AuthConn, items: Vec<&Self::Partial>) -> bool;
    fn delete_by_id(connection: &AuthConn, id: TypedRecordId<Self>) -> bool;
}
