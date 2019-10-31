mod types;
use enforcement::*;
fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod test {
    use crate::*;
    use types::*;

    #[test]
    fn insert_then_read() {
        let db_conn = DBConn::new("test2");

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

        let uids = User::insert_many(db_conn.as_princ(Principle::Public), users).unwrap();
        let (uid_alex, _uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };

        let retrieved_alex = User::find_by_id(
            db_conn.as_princ(Principle::Id(uid_alex.clone())),
            uid_alex.clone(),
        )
        .unwrap();
        let publicly_retrieved_alex =
            User::find_by_id(db_conn.as_princ(Principle::Public), uid_alex.clone()).unwrap();

        assert_eq!(Some("alex_hash".to_string()), retrieved_alex.pass_hash);
        assert_eq!(None, publicly_retrieved_alex.pass_hash);
    }

    #[test]
    fn set_password() {
        let db_conn = DBConn::new("test2");
        let alex_id = User::insert_many(
            db_conn.as_princ(Principle::Public),
            vec![user! {username: "Alex".to_string(),
                        pass_hash: "alex_hash".to_string(),
                        num_followers: 0,
            }],
        )
        .unwrap()
        .pop()
        .expect("Didn't get any ids back!");
        let mut alex_obj =
            User::find_by_id(db_conn.as_princ(Principle::Public), alex_id.clone()).unwrap();

        // Write only the pass hash
        alex_obj.pass_hash = Some("monster_mash".to_string());
        alex_obj.username = None;
        alex_obj.num_followers = None;

        assert!(!alex_obj.save(db_conn.as_princ(Principle::Public)));
        {
            let retrieved_alex = User::find_by_id(
                db_conn.as_princ(Principle::Id(alex_id.clone())),
                alex_id.clone(),
            )
            .unwrap();
            let publicly_retrieved_alex =
                User::find_by_id(db_conn.as_princ(Principle::Public), alex_id.clone()).unwrap();

            assert_eq!(Some("alex_hash".to_string()), retrieved_alex.pass_hash);
            assert_eq!(None, publicly_retrieved_alex.pass_hash);
        }
        assert!(alex_obj.save(db_conn.as_princ(Principle::Id(alex_id.clone()))));

        {
            let retrieved_alex = User::find_by_id(
                db_conn.as_princ(Principle::Id(alex_id.clone())),
                alex_id.clone(),
            )
            .unwrap();
            let publicly_retrieved_alex =
                User::find_by_id(db_conn.as_princ(Principle::Public), alex_id.clone()).unwrap();

            assert_eq!(Some("monster_mash".to_string()), retrieved_alex.pass_hash);
            assert_eq!(None, publicly_retrieved_alex.pass_hash);
        }
    }
}
