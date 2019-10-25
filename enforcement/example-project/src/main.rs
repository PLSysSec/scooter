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
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
            },
        ];

        let uids = User::insert_many(db_conn.as_princ(Principle::Public), users).unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };

        let retrieved_alex =
            User::find_by_id(db_conn.as_princ(Principle::Public), uid_alex.clone()).unwrap();

        assert_eq!(
            "alex_hash",
            retrieved_alex
                .get_pass_hash(&Principle::Id(uid_alex.clone()))
                .unwrap()
        );
        assert_eq!(
            None,
            retrieved_alex.get_pass_hash(&Principle::Id(uid_john.clone()))
        );
    }

    #[test]
    fn set_password() {
        let db_conn = DBConn::new("test2");
        let alex_id = User::insert_many(
            db_conn.as_princ(Principle::Public),
            vec![user! {username: "Alex".to_string(),
            pass_hash: "alex_hash".to_string(),}],
        )
        .unwrap()
        .pop()
        .expect("Didn't get any ids back!");
        let mut alex_obj =
            User::find_by_id(db_conn.as_princ(Principle::Public), alex_id.clone()).unwrap();
        alex_obj.set_pass_hash("monster_mash".to_string());
        assert!(
            alex_obj.save(
                db_conn.as_princ(Principle::Id(alex_id.clone())),
                vec! [UserFields::Pass_hash]));
        assert!(
            !alex_obj.save(
                db_conn.as_princ(Principle::Public),
                vec! [UserFields::Pass_hash]));
    }
}
