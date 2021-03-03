mod migrate;
pub use crate::migrate::*;
#[cfg(test)]
mod tests {
    use super::*;
    use bson::{bson, doc, Bson, Document};
    use std::fs::read_to_string;

    mod types;
    use enforcement::*;
    use types::*;

    use crate::migrate::migrate;

    use std::env::current_dir;
    use std::path::Path;
    fn get_dbconn(db_name: &String) -> DBConn {
        let db_conf = &DbConf {
            host: "localhost".to_string(),
            port: 27017,
            db_name: db_name.clone(),
        };
        let db_conn = DBConn::new(&db_conf.host, db_conf.port, &db_conf.db_name);
        db_conn.mongo_conn.collection("User").drop(None).ok();
        db_conn.mongo_conn.collection("Message").drop(None).ok();
        db_conn.mongo_conn.collection("InvitedUser").drop(None).ok();
        reset_migration_history(db_conf);
        db_conn
            .mongo_conn
            .collection("migrations-run")
            .drop(None)
            .ok();
        db_conn
    }
    #[test]
    fn add_and_remove_fields() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "add_and_remove_fields_test".to_string();
        let db_conn = get_dbconn(&db_name);

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 0,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        // Insert the users into the database, and get back their ids
        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string removes the num_followers
        // column from the schema.
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(
                Path::new(&std::env::current_dir().unwrap()).join("policy.txt".to_string()),
            )
            .unwrap(),
            r#"
                User::RemoveField(num_followers)
                User::AddField(num_friends: I64 {read: public, write: none,}, u -> 1337)
                User::AddField(num_roomates: I64 {read: public, write: none,}, u -> 0)
                User::RemoveField(num_roomates)
                "#,
            "test_migration",
        )
        .expect("migration failed");
        // Pull out the resulting docs, using the ids we got when we
        // inserted the originals.
        let alex_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_alex.clone()}), None)
            .unwrap()
            .unwrap();
        let john_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_john.clone()}), None)
            .unwrap()
            .unwrap();

        // Make sure the right things got removed
        assert!(!alex_result_doc.contains_key("num_followers"));
        assert!(!john_result_doc.contains_key("num_followers"));

        assert!(!alex_result_doc.contains_key("num_roomates"));
        assert!(!john_result_doc.contains_key("num_roomates"));

        // Make sure nothing else got removed
        assert_eq!(
            alex_result_doc
                .get_str("username")
                .expect("Couldn't find username key after migration"),
            "Alex"
        );
        assert_eq!(
            john_result_doc
                .get_str("username")
                .expect("Couldn't find username key after migration"),
            "John"
        );
        assert_eq!(
            alex_result_doc
                .get_str("pass_hash")
                .expect("Couldn't find pass_hash key after migration"),
            "alex_hash"
        );
        assert_eq!(
            john_result_doc
                .get_str("pass_hash")
                .expect("Couldn't find pass_hash key after migration"),
            "john_hash"
        );
        // Make sure the added fields got added with the right values
        assert_eq!(
            alex_result_doc
                .get_i64("num_friends")
                .expect("Couldn't find pass_hash key after migration"),
            1337
        );
        assert_eq!(
            john_result_doc
                .get_i64("num_friends")
                .expect("Couldn't find pass_hash key after migration"),
            1337
        );
    }
    #[test]
    fn rename_field_addrm() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "rename_field_addrm_test".to_string();
        let db_conn = get_dbconn(&db_name);

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 42,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        // Insert the users into the database, and get back their ids
        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string removes the num_followers
        // column from the schema.
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(
                std::env::current_dir()
                    .unwrap()
                    .join("policy.txt".to_string()),
            )
            .unwrap(),
            r#"
                User::AddField(num_friends: I64 { read: public, write: none, }, u -> u.num_followers)
                User::RemoveField(num_followers)
                "#,
            "test_migration",
        ).expect("migration failed");
        // Pull out the resulting docs, using the ids we got when we
        // inserted the originals.
        let alex_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_alex.clone()}), None)
            .unwrap()
            .unwrap();
        let john_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_john.clone()}), None)
            .unwrap()
            .unwrap();

        // Make sure the right things got removed
        assert!(!alex_result_doc.contains_key("num_followers"));
        assert!(!john_result_doc.contains_key("num_followers"));
        // Make sure the added fields got the right values
        assert_eq!(
            alex_result_doc
                .get_i64("num_friends")
                .expect("Couldn't find pass_hash key after migration"),
            42
        );
        assert_eq!(
            john_result_doc
                .get_i64("num_friends")
                .expect("Couldn't find pass_hash key after migration"),
            0
        );
    }
    #[test]
    fn duplicate_users() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "duplicate_messages_test".to_string();
        let db_conn = get_dbconn(&db_name);

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 42,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        // Insert the users into the database, and get back their ids
        let _uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string duplicates users.
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(current_dir().unwrap().join("policy.txt")).unwrap(),
            r#"
                User::ForEach(u -> User::Create(User {username: u.username + "_duplicate"
                                                      ...u}))
                "#,
            "test_migration",
        )
        .expect("migration failed");
        // Make sure there are now double the users.
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            4
        );
        let all_docs: Vec<Document> = db_conn
            .mongo_conn
            .collection(&col_name)
            .find(None, None)
            .unwrap()
            .into_iter()
            .map(|d| d.unwrap())
            .collect();
        let alex_duplicate = all_docs
            .iter()
            .find(|doc| doc.get_str("username") == Ok("Alex_duplicate"))
            .expect("Couldn't find alex duplicate doc!");
        assert_eq!(alex_duplicate.get_str("pass_hash"), Ok("alex_hash"));
        assert_eq!(alex_duplicate.get_i64("num_followers"), Ok(42));
    }
    #[test]
    fn delete_users() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "delete_users_test".to_string();
        let db_conn = get_dbconn(&db_name);

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 42,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        // Insert the users into the database, and get back their ids
        let _uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string duplicates users.
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(current_dir().unwrap().join("policy.txt")).unwrap(),
            r#"
                User::ForEach(u -> User::Delete(u.id))
                "#,
            "test_migration",
        )
        .expect("migration failed");
        // Make sure there are now double the users.
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            0
        );
    }
    #[test]
    fn sub_half_follower() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "add_half_follower_test".to_string();
        let db_conn = get_dbconn(&db_name);

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 42,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string duplicates users.
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(current_dir().unwrap().join("policy.txt")).unwrap(),
            r#"
                User::ChangeField(num_followers, F64, u -> u.num_followers - 0.5)
                "#,
            "test_migration",
        )
        .expect("migration failed");
        // Pull out the resulting docs, using the ids we got when we
        // inserted the originals.
        let alex_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_alex.clone()}), None)
            .unwrap()
            .unwrap();
        let john_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_john.clone()}), None)
            .unwrap()
            .unwrap();
        // Make sure the changes were made
        assert_eq!(
            alex_result_doc
                .get_f64("num_followers")
                .expect("Couldn't find pass_hash key after migration"),
            41.5
        );
        assert_eq!(
            john_result_doc
                .get_f64("num_followers")
                .expect("Couldn't find pass_hash key after migration"),
            -0.5
        );
    }
    #[test]
    fn rename_field() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "rename_field_test".to_string();
        let db_conn = get_dbconn(&db_name);

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 42,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        // Insert the users into the database, and get back their ids
        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string removes the num_followers
        // column from the schema.
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(current_dir().unwrap().join("policy.txt")).unwrap(),
            r#"
                User::RenameField(num_followers, num_friends)
                "#,
            "test_migration",
        )
        .expect("migration failed");
        // Pull out the resulting docs, using the ids we got when we
        // inserted the originals.
        let alex_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_alex.clone()}), None)
            .unwrap()
            .unwrap();
        let john_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_john.clone()}), None)
            .unwrap()
            .unwrap();

        // Make sure the old name doesn't exist
        assert!(!alex_result_doc.contains_key("num_followers"));
        assert!(!john_result_doc.contains_key("num_followers"));

        // Make sure the new name exists with the same value.
        assert_eq!(
            alex_result_doc
                .get_i64("num_friends")
                .expect("Couldn't find num_friends key after migration"),
            42
        );
        assert_eq!(
            john_result_doc
                .get_i64("num_friends")
                .expect("Couldn't find num_friends key after migration"),
            0
        );
    }
    #[test]
    fn create_parallel_collection() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "create_parallel_collection_test".to_string();
        let db_conn = get_dbconn(&db_name);

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 42,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        // Insert the users into the database, and get back their ids
        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let (uid_alex, _uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string.
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(current_dir().unwrap().join("policy.txt")).unwrap(),
            r#"
                CreateCollection(Phone {create: public, delete: public, owner: Id(User) { read: public, write: none,},})
                User::ForEach(u -> Phone::Create(Phone {owner: u.id}))
                "#,
            "test_migration",
        ).expect("migration failed");
        let all_phones: Vec<Document> = db_conn
            .mongo_conn
            .collection("Phone")
            .find(None, None)
            .unwrap()
            .into_iter()
            .map(|d| d.unwrap())
            .collect();
        let _alex_phone = all_phones
            .iter()
            .find(|doc| {
                RecordId::from_object_id(doc.get_object_id("owner").unwrap().clone())
                    == uid_alex.clone().into()
            })
            .expect("Couldn't find alex phone !");
    }
    #[test]
    fn enable_multiple_usernames() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "enable_multiple_usernames_test".to_string();
        let db_conn = get_dbconn(&db_name);

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 42,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        // Insert the users into the database, and get back their ids
        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let (uid_alex, _uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string removes the num_followers
        // column from the schema.
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(current_dir().unwrap().join("policy.txt")).unwrap(),
            r#"
                User::ChangeField(username, Set(String), u -> [u.username, u.username + "_alias"])
                "#,
            "test_migration",
        )
        .expect("migration failed");
        // Pull out one of the resulting docs, using the ids we got when we
        // inserted the originals.
        let alex_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_alex.clone()}), None)
            .unwrap()
            .unwrap();

        // Make sure both the usernames are there
        assert_eq!(
            alex_result_doc
                .get_array("username")
                .expect("Couldn't find username key after migration"),
            &vec![bson!("Alex"), bson!("Alex_alias")]
        );
    }

    #[test]
    fn stamp_messages() {
        // The name of the message collection
        let mcol_name = "Message".to_string();
        // Create a connection to the database
        let db_name = "stamp_messages_test".to_string();
        let db_conn = get_dbconn(&db_name);

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 42,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        // Insert the users into the database, and get back their ids
        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        // Make connection objects for both users
        let alex_conn = &db_conn
            .clone()
            .as_princ(Principal::Id(uid_alex.clone().into()));
        let john_conn = &db_conn
            .clone()
            .as_princ(Principal::Id(uid_john.clone().into()));

        let m1_id = Message::insert_one(
            alex_conn,
            message! { from: uid_alex.clone(),
            to: uid_john.clone(),
            text: "Suuuup boi".to_string() },
        )
        .unwrap();
        let m2_id = Message::insert_one(
            john_conn,
            message! { from: uid_john.clone(),
            to: uid_alex.clone(),
            text: "Yo".to_string() },
        )
        .unwrap();
        let m3_id = Message::insert_one(
            alex_conn,
            message! { from: uid_alex.clone(),
            to: uid_john.clone(),
            text: "Whatchu up to tn?".to_string() },
        )
        .unwrap();
        let m4_id = Message::insert_one(
            john_conn,
            message! { from: uid_john.clone(),
            to: uid_alex.clone(),
            text: "literally nothing".to_string() },
        )
        .unwrap();

        migrate(
            DbConf { host: "localhost".to_string(), port: 27017, db_name},
            &read_to_string(current_dir().unwrap().join("policy.txt")).unwrap(),
            r#"
                Message::AddField(popular_sender: Bool {read: public, write: none,}, m -> (if User::ById(m.from).num_followers < 20 then false else true))
                "#,
            "test_migration",
        ).expect("migration failed");

        let m1_doc = db_conn
            .mongo_conn
            .collection(&mcol_name)
            .find_one(Some(doc! {"_id": m1_id}), None)
            .expect("Failed to retreive message #1 doc")
            .expect("Failed to retreive message #1 doc (2)");

        assert_eq!(m1_doc.get_bool("popular_sender").unwrap(), true);

        let m2_doc = db_conn
            .mongo_conn
            .collection(&mcol_name)
            .find_one(Some(doc! {"_id": m2_id}), None)
            .expect("Failed to retreive message #2 doc")
            .expect("Failed to retreive message #2 doc (2)");

        assert_eq!(m2_doc.get_bool("popular_sender").unwrap(), false);

        let m3_doc = db_conn
            .mongo_conn
            .collection(&mcol_name)
            .find_one(Some(doc! {"_id": m3_id}), None)
            .expect("Failed to retreive message #3 doc")
            .expect("Failed to retreive message #3 doc (2)");

        assert_eq!(m3_doc.get_bool("popular_sender").unwrap(), true);

        let m4_doc = db_conn
            .mongo_conn
            .collection(&mcol_name)
            .find_one(Some(doc! {"_id": m4_id}), None)
            .expect("Failed to retreive message #2 doc")
            .expect("Failed to retreive message #2 doc (2)");

        assert_eq!(m4_doc.get_bool("popular_sender").unwrap(), false);
    }
    #[test]
    fn identity_using_map() {
        // The name of the users collection
        let mcol_name = "MultiMessage".to_string();
        // Create a connection to the database
        let db_name = "identity_using_map_test".to_string();
        let db_conn = get_dbconn(&db_name);
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 42,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        // Insert the users into the database, and get back their ids
        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        let alex_conn = &db_conn
            .clone()
            .as_princ(Principal::Id(uid_alex.clone().into()));
        let m_id = MultiMessage::insert_one(
            alex_conn,
            multimessage! { from: uid_alex.clone(),
            to: vec![uid_john.clone(), uid_alex.clone()],
            text: "Suuuup everyone".to_string() },
        )
        .unwrap();
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(current_dir().unwrap().join("policy.txt")).unwrap(),
            r#"
                     MultiMessage::ChangeField(to, Set(Id(User)), u -> u.to.map(id -> id))
                     "#,
            "test_migration",
        )
        .expect("migration failed");
        let m_doc = db_conn
            .mongo_conn
            .collection(&mcol_name)
            .find_one(Some(doc! {"_id": m_id}), None)
            .expect("Failed to retreive message #1 doc")
            .expect("Failed to retreive message #1 doc (2)");
        let resulting_to = m_doc.get_array("to").unwrap();
        assert_eq!(resulting_to.len(), 2);
        match (&resulting_to[0], &resulting_to[1]) {
            (Bson::ObjectId(first), Bson::ObjectId(second)) => {
                assert_eq!(TypedRecordId::<User>::from(first.clone()), *uid_john);
                assert_eq!(TypedRecordId::<User>::from(second.clone()), *uid_alex);
            }
            _ => panic!("result wasn't the right type!"),
        };
    }
    #[test]
    fn add_field_self_reference_policy() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "add_field_self_reference_policy_test".to_string();
        let db_conn = get_dbconn(&db_name);

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 0,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
            },
        ];
        // Insert the users into the database, and get back their ids
        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count_documents(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string removes the num_followers
        // column from the schema.
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(
                Path::new(&std::env::current_dir().unwrap()).join("policy.txt".to_string()),
            )
            .unwrap(),
            r#"User::AddField(is_admin: Bool {
                              read: _ -> User::Find({}).map(u -> u.id),
                              write: _ -> User::Find({is_admin: true}).map(u -> u.id),
                              }, _ -> false)
                "#,
            "test_migration",
        )
        .expect("migration failed");
        // Pull out the resulting docs, using the ids we got when we
        // inserted the originals.
        let alex_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_alex.clone()}), None)
            .unwrap()
            .unwrap();
        let john_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_john.clone()}), None)
            .unwrap()
            .unwrap();

        // Make sure the added fields got added with the right values
        assert_eq!(
            alex_result_doc
                .get_bool("is_admin")
                .expect("Couldn't find is_admin key after migration"),
            false
        );
        assert_eq!(
            john_result_doc
                .get_bool("is_admin")
                .expect("Couldn't find is_admin key after migration"),
            false
        );
    }
    #[test]
    fn add_field_self_reference_id() {
        // The name of the collection
        let col_name = "InvitedUser".to_string();
        // Create a connection to the database
        let db_name = "add_field_self_reference_id".to_string();
        let db_conn = get_dbconn(&db_name);

        let alex_uid = InvitedUser::insert_one(
            &db_conn.clone().as_princ(Principal::Unauthenticated),
            inviteduser! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                inviter: POption::None,
            },
        )
        .unwrap();

        let john_uid = InvitedUser::insert_one(
            &db_conn.clone().as_princ(Principal::Unauthenticated),
            inviteduser! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                inviter: POption::Some(alex_uid.clone()),
            },
        )
        .unwrap();
        // Perform a migration, the contents of the policy file, and
        // this migration string. The string removes the num_followers
        // column from the schema.
        migrate(
            DbConf {
                host: "localhost".to_string(),
                port: 27017,
                db_name,
            },
            &read_to_string(
                Path::new(&std::env::current_dir().unwrap()).join("policy.txt".to_string()),
            )
            .unwrap(),
            r#"InvitedUser::AddField(inviter_name: String {
                                        read: public,
                                        write: none,
                                     }, u -> (match u.inviter as x in InvitedUser::ById(x).username else ""))
                "#,
            "test_migration",
        ).expect("migration failed");
        // Pull out the resulting docs, using the ids we got when we
        // inserted the originals.
        let alex_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": alex_uid.clone()}), None)
            .unwrap()
            .unwrap();
        let john_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": john_uid.clone()}), None)
            .unwrap()
            .unwrap();

        // Make sure the added fields got added with the right values
        assert_eq!(
            alex_result_doc
                .get_str("inviter_name")
                .expect("Couldn't find inviter key after migration"),
            ""
        );
        assert_eq!(
            john_result_doc
                .get_str("inviter_name")
                .expect("Couldn't find inviter key after migration"),
            "Alex"
        );
    }
}
