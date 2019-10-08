use mongodb::oid::ObjectId;
use mongodb::{bson, doc};

type PrincipleId = ObjectId;

#[derive(Debug)]
pub enum PolicyValue {
    Public,
    Ids(Vec<PrincipleId>),
}
impl PolicyValue {
    fn accessible_by(&self, user: &PrincipleId) -> bool {
        match self {
            Self::Public => true,
            Self::Ids(ids) => ids.iter().find(|&el| *el == *user).is_some(),
        }
    }
}

trait MongoDocument {
    fn from_document(doc: mongodb::Document) -> Self;
    fn to_document(&self) -> mongodb::Document;
}

// ----- THIS SHOULD ALL BE GENERATED ------
pub struct User {
    username: String,
    pass_hash: String,
    id: Option<ObjectId>,
}

/// A convenience struct that contains all viewable fields
#[derive(Debug)]
pub struct ResolvedUser {
    pub username: Option<String>,
    pub pass_hash: Option<String>,
    pub id: Option<ObjectId>
}

mod user_policies {
    use super::*;
    pub fn pass_hash(u: &User) -> PolicyValue {
        PolicyValue::Ids(u.id.iter().cloned().collect())
    }

    pub fn username(_: &User) -> PolicyValue {
        PolicyValue::Public
    }
}

impl User {
    pub fn fully_resolve(&self, id: &PrincipleId) -> ResolvedUser {
        ResolvedUser {
            username: self.get_username(id).map(|s| s.clone()),
            pass_hash: self.get_pass_hash(id).map(|s| s.clone()),
            id: self.id.clone()
        }
    }

    pub fn get_username(&self, id: &PrincipleId) -> Option<&String> {
        if !user_policies::username(self).accessible_by(id) {
            None
        } else {
            Some(&self.username)
        }
    }

    pub fn get_pass_hash(&self, id: &PrincipleId) -> Option<&String> {
        if !user_policies::pass_hash(self).accessible_by(id) {
            None
        } else {
            Some(&self.pass_hash)
        }

    }
}

impl MongoDocument for User {
    fn from_document(doc: mongodb::Document) -> Self {
        User {
            username: doc.get_str("username").unwrap().to_string(),
            pass_hash: doc.get_str("pass_hash").unwrap().to_string(),
            id: Some(doc.get_object_id("_id").unwrap().clone()),
        }
    }
    fn to_document(&self) -> mongodb::Document {
        let mut doc = doc! {
            "username": &self.username,
            "pass_hash": &self.pass_hash,
        };
        if let Some(id) = &self.id {
            doc.insert("_id", id.clone());
        };
        doc
    }
}

// -------- END GENERATED ------


#[cfg(test)]
mod test {
    use mongodb::coll::Collection;
    use mongodb::db::ThreadedDatabase;
    use mongodb::Client;
    use mongodb::ThreadedClient;
    use crate::*;

    #[allow(unused_must_use)]
    fn setup_db() -> (Collection) {

        let client = Client::connect("localhost", 27017).expect("Failed to initialize client.");
        let db = client.db("test");

        // Clean out the collection
        db.drop_collection("User");
        db.create_collection("User", None);

        // Return ref to collection
        db.collection("User")
    }

    #[test]
    fn insert_then_read() {
        let user_coll = setup_db();
        let users: Vec<_> = [User {
            username: "Alex".to_string(),
            pass_hash: "alex_hash".to_string(),
            id: None,
        },
            User {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                id: None,
            } 
        ].into_iter().map(User::to_document).collect();

        let insert_res = user_coll
            .insert_many(users, None)
            .unwrap()
            .inserted_ids
            .unwrap();

        let mut uids = insert_res.values().map(|b| b.as_object_id().unwrap());
        let uid_alex = uids.next().unwrap();
        let uid_john = uids.next().unwrap();

        let retrieved_doc = user_coll
            .find_one(Some(doc! {"_id": uid_alex.clone()}), None)
            .unwrap()
            .unwrap();

        let retrieved_alex = User::from_document(retrieved_doc);

        assert_eq!("alex_hash", retrieved_alex.get_pass_hash(&uid_alex).unwrap());
        assert_eq!(None, retrieved_alex.get_pass_hash(&uid_john));
    }
}
