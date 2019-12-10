use std::io::{self, Read};
use std::path::Path;

mod migrate;
use migrate::migrate;

fn main() {
    // Grab the argument to the binary
    let mut args = std::env::args();
    args.next().expect("Not enough arguments");
    // Arguments are the database name, the policy file, the migration file
    let db_name = args.next().expect("Not enough arguments");
    let policy_file = args.next().expect("Not enough arguments");
    let migration_file = args.next().expect("Not enough arguments");
    // Call the main migration function
    migrate(
        db_name,
        get_contents(Path::new(&policy_file)).expect("Couldn't open policy file"),
        get_contents(Path::new(&migration_file)).expect("Couldn't open migration file"),
    );
}
/// Returns the contents of the file at a given path
///
/// # Arguments
/// * `fname` - The path to the file to read
fn get_contents(fname: &Path) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
}
#[cfg(test)]
mod tests {
    use super::*;
    use mongodb::db::ThreadedDatabase;
    use mongodb::{bson, doc};

    mod types;
    use enforcement::*;
    use std::path::Path;
    use types::*;
    #[test]
    fn add_and_remove_fields() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "add_and_remove_fields_test".to_string();
        let db_conn = DBConn::new(&db_name);
        // Drop any existing collection by the same name, so that the
        // collection is empty.
        db_conn.mongo_conn.collection(&col_name).drop().unwrap();

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
        let uids = User::insert_many(&db_conn.as_princ(Principle::Public), users).unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string removes the num_followers
        // column from the schema.
        migrate(
            db_name,
            get_contents(
                Path::new(&std::env::current_dir().unwrap())
                    .join("policy.txt".to_string())
                    .as_ref(),
            )
            .unwrap(),
            r#"
                User::RemoveField(num_followers)
                User::AddField(num_friends, I64, u -> 1337)
                User::AddField(num_roomates, I64, u -> 0)
                User::RemoveField(num_roomates)
                "#
            .to_string(),
        );
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
    fn rename_field() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_name = "rename_field_test".to_string();
        let db_conn = DBConn::new(&db_name);
        // Drop any existing collection by the same name, so that the
        // collection is empty.
        let coll = db_conn.mongo_conn.collection(&col_name);
        coll.drop().unwrap();
        assert_eq!(coll.count(None, None).unwrap(), 0);

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
        let uids = User::insert_many(&db_conn.as_princ(Principle::Public), users).unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string removes the num_followers
        // column from the schema.
        migrate(
            db_name,
            get_contents(
                Path::new(&std::env::current_dir().unwrap())
                    .join("policy.txt".to_string())
                    .as_ref(),
            )
            .unwrap(),
            r#"
                User::AddField(num_friends, I64, u -> u.num_followers)
                User::RemoveField(num_followers)
                "#
            .to_string(),
        );
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
        let db_conn = DBConn::new(&db_name);
        // Drop any existing collection by the same name, so that the
        // collection is empty.
        let coll = db_conn.mongo_conn.collection(&col_name);
        coll.drop().unwrap();
        assert_eq!(coll.count(None, None).unwrap(), 0);

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
        let _uids = User::insert_many(&db_conn.as_princ(Principle::Public), users).unwrap();
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count(None, None)
                .unwrap(),
            2
        );

        // Perform a migration, the contents of the policy file, and
        // this migration string. The string duplicates users.
        migrate(
            db_name,
            get_contents(
                Path::new(&std::env::current_dir().unwrap())
                    .join("policy.txt".to_string())
                    .as_ref(),
            )
            .unwrap(),
            r#"
                User::ForEach(u -> User::Create(User {username: u.username,
                                                      pass_hash: u.pass_hash,
                                                      num_followers: u.num_followers,}))
                "#
            .to_string(),
        );
        // Make sure there are now double the users.
        assert_eq!(
            db_conn
                .mongo_conn
                .collection(&col_name)
                .count(None, None)
                .unwrap(),
            4
        );
    }
}
