mod types;
use enforcement::*;
fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod test {
    use crate::*;
    use types::*;
    use mongodb::coll::Collection;
    use mongodb::db::ThreadedDatabase;
    use mongodb::Client;
    use mongodb::ThreadedClient;

    #[test]
    fn insert_then_read() {
        let user_coll = CheckedCollection::new("test2");
        let users: Vec<_> = [
            User::new(UserProps{username: "Alex".to_string(),
                                pass_hash: "alex_hash".to_string()}),
            User::new(UserProps{username: "John".to_string(),
                                pass_hash: "john_hash".to_string()})
        ]
        .into_iter()
        .map(User::to_document)
        .collect();

        let mut uids = user_coll.insert_many(users).unwrap();
        let (uid_alex, uid_john) =
            match uids.as_slice() {
                [id1, id2] => (id1, id2),
                _ => panic!("Not the right number of returned ids")
            };

        let retrieved_doc = user_coll
            .find_one(doc! {"_id": uid_alex.clone()})
            .unwrap();

        let retrieved_alex = User::from_document(retrieved_doc);

        assert_eq!(
            "alex_hash",
            retrieved_alex.get_pass_hash(&uid_alex).unwrap()
        );
        assert_eq!(None, retrieved_alex.get_pass_hash(&uid_john));
    }
}
