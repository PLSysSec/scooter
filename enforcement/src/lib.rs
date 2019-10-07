use mongodb::Client;
use mongodb::ThreadedClient;
use mongodb::db::ThreadedDatabase;
use mongodb::{Bson, bson, doc};
use mongodb::oid::ObjectId;
use fmt;

fn main() {
    // Direct connection to a server. Will not look for other servers in the topology.
    println!("Hello, world!");
}

type PrincipleId = ObjectId;

#[derive(Debug)]
struct User {
    username : PolicyGated<String>,
    pass_hash : PolicyGated<String>,
    id : Option<ObjectId>,
}
trait MongoDocument {
    fn from_document(doc : mongodb::Document) -> Self;
    fn to_document(&self) -> mongodb::Document;
}
impl MongoDocument for User {
    fn from_document(doc : mongodb::Document) -> Self {
        User{username: PolicyGated::new(doc.get_str("username").unwrap().to_string()),
             pass_hash: PolicyGated::new(doc.get_str("pass_hash").unwrap().to_string()),
             id:Some(doc.get_object_id("_id").unwrap().clone())}
    }
    fn to_document(&self) -> mongodb::Document {
        let mut doc = doc! {
            "username": &self.username.value,
            "pass_hash": &self.pass_hash.value,
        };
        if let Some(id) = &self.id {
            doc.insert("_id", id.clone());
        };
        doc
    }
}
#[derive(Debug)]
enum PolicyValue {
    Public,
    Ids(Vec<PrincipleId>),
}
impl PolicyValue {
    fn can_access(&self, user : PrincipleId) -> bool {
        match self {
            Self::Public=> true,
            Self::Ids(ids) => ids.iter().find(|&el| *el==user).is_some(),
        }
    }
}
struct PolicyGated<R, F : fmt::Debug> {
    value : F,
    read_policy : fn(&R) -> PolicyValue,
}
impl <R, F : fmt::Debug> fmt::Debug for PolicyGated<R, F>{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PolicyGated {{ value: {} }}", self.value)
    }
}

impl <R, F : fmt::Debug> PolicyGated<R, F> {
    fn read(&self, id: PrincipleId) -> Option<&T> {
        if self.read_policy(self.value){
        }
        Some(&self.value)
    }
    fn new(value : T) -> Self {
        PolicyGated{value}
    }
}

fn userPassHashPolicy(u : &User) -> PolicyValue {
    PolicyValue::Ids(vec![u.id])
}

fn publicPolicy(u : &User) -> PolicyValue {
    PolicyValue::Public
}

#[test]
fn create_database() {
    let client = Client::connect("localhost", 27017)
        .expect("Failed to initialize client.");
    let db = client.db("test");
    db.create_collection("User", None);
    let user_coll = db.collection("User");
    let u = User{username: "Alex".to_string(), pass_hash: "hey".to_string(), id:None};
    let u_id = user_coll.insert_one(u.to_document(), None).unwrap().inserted_id.unwrap();
    let retrieved_doc = user_coll.find_one(Some(doc!{"_id": u_id}), None).unwrap().unwrap();
    println!("{:?}", retrieved_doc);
    let retrieved_user : User = User::from_document(retrieved_doc);
    println!("{:?}", retrieved_user);
    assert!(false);
}
