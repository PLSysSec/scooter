mod types;

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod test {
    use enforcement::*;
    use crate::*;
    use types::*;

    #[test]
    fn insert_then_read() {
        let db_conn = get_dbconn();

        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 0,
                trustworthyness: 15,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
                trustworthyness: 5,
            },
        ];

        let uids = User::insert_many(&db_conn.clone().as_princ(Principle::Unauthenticated), users).unwrap();
        let (uid_alex, _uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };

        let retrieved_alex = User::find_by_id(
            &db_conn.clone().as_princ(Principle::Id(uid_alex.clone().into())),
            uid_alex.clone().into(),
        )
        .unwrap();
        let publicly_retrieved_alex = User::find_by_id(
            &db_conn.clone().as_princ(Principle::Unauthenticated),
            uid_alex.clone().into(),
        )
        .unwrap();

        assert_eq!(Some("alex_hash".to_string()), retrieved_alex.pass_hash);
        assert_eq!(None, publicly_retrieved_alex.pass_hash);
    }

    #[test]
    fn set_password() {
        let db_conn = get_dbconn();
        let alex_id = User::insert_many(
            &db_conn.clone().as_princ(Principle::Unauthenticated),
            vec![user! {username: "Alex".to_string(),
                        pass_hash: "alex_hash".to_string(),
                        num_followers: 0,
                        trustworthyness: 15,
            }],
        )
        .unwrap()
        .pop()
        .expect("Didn't get any ids back!");

        // Write only the pass hash
        let alex_obj = BuildUser::new(alex_id.clone().into())
            .pass_hash("monster_mash".to_string())
            .finalize();

        assert!(!alex_obj.save(&db_conn.clone().as_princ(Principle::Unauthenticated)));
        {
            let retrieved_alex = User::find_by_id(
                &db_conn.clone().as_princ(Principle::Id(alex_id.clone().into())),
                alex_id.clone().into(),
            )
            .unwrap();
            let publicly_retrieved_alex =
                User::find_by_id(&db_conn.clone().as_princ(Principle::Unauthenticated), alex_id.clone().into())
                    .unwrap();

            assert_eq!(Some("alex_hash".to_string()), retrieved_alex.pass_hash);
            assert_eq!(None, publicly_retrieved_alex.pass_hash);
        }
        assert!(alex_obj.save(&db_conn.clone().as_princ(Principle::Id(alex_id.clone().into()))));

        {
            let retrieved_alex = User::find_by_id(
                &db_conn.clone().as_princ(Principle::Id(alex_id.clone().into())),
                alex_id.clone().into(),
            )
            .unwrap();
            let publicly_retrieved_alex =
                User::find_by_id(&db_conn.clone().as_princ(Principle::Unauthenticated), alex_id.clone().into())
                    .unwrap();

            assert_eq!(Some("monster_mash".to_string()), retrieved_alex.pass_hash);
            assert_eq!(None, publicly_retrieved_alex.pass_hash);
        }
    }

    #[test]
    fn fail_delete_user() {
        let db_conn = get_dbconn();

        let alex_id = User::insert_many(
            &db_conn.clone().as_princ(Principle::Unauthenticated),
            vec![user! {username: "Alex".to_string(),
                        pass_hash: "alex_hash".to_string(),
                        num_followers: 0,
                        trustworthyness: 15,
            }],
        )
        .unwrap()
        .pop()
        .expect("Didn't get any ids back!");

        let result = User::delete_by_id(
            &db_conn.clone().as_princ(Principle::Id(alex_id.clone().into())),
            alex_id.clone().into(),
        );
        assert!(!result);
    }

    fn get_dbconn() -> DBConn {
        let db_conn = DBConn::new("localhost", 27017,"test2");
        db_conn.mongo_conn.collection("User").drop(None).ok();
        db_conn.mongo_conn.collection("Message").drop(None).ok();
        db_conn
    }

    #[test]
    fn set_from_trustworthy() {
        let db_conn = get_dbconn();

        // Add two users, alex and john, where alex has a
        // trustworthyness above ten, and john has one below ten.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 0,
                trustworthyness: 15,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
                trustworthyness: 5,
            },
        ];

        // Insert the users, and get their ids
        let uids = User::insert_many(&db_conn.clone().as_princ(Principle::Unauthenticated), users).unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        // Make connection objects for both users
        let alex_conn = &db_conn.clone().as_princ(Principle::Id(uid_alex.clone().into()));
        let john_conn = &db_conn.clone().as_princ(Principle::Id(uid_john.clone().into()));

        // Insert a message from alex to john, and get its id
        let mid_fromalex = Message::insert_one(
            alex_conn,
            message! {
                from: uid_alex.clone(),
                to: uid_john.clone(),
                text: "Hey, how's it hanging dude?".to_string()
            },
        )
        .expect("Couldn't insert message from alex");
        // Insert a message from john to alex, and get its id
        let mid_fromjohn = Message::insert_one(
            john_conn,
            message! {
                from: uid_john.clone(),
                to: uid_alex.clone(),
                text: "Not too bad, how about yourself?".to_string()
            },
        )
        .expect("Couldn't insert message from john");
        // Try to insert a message from john to himself, as alex, and
        // make sure it fails.
        let impersonator_message = message! {
            from: uid_john.clone(),
            to: uid_john.clone(),
            text: "Blah blah blah, I'm a John and I know things".to_string(),
        };
        assert!(Message::insert_many(alex_conn, vec![impersonator_message]).is_none());

        // Make sure we can successfully set the "from" as alex
        let fromalex_fromjohn_obj = BuildMessage::new(mid_fromalex.clone().into())
            .from(uid_john.clone())
            .finalize();

        assert!(fromalex_fromjohn_obj.save(alex_conn));
        {
            // Retrieve the message as john (alex should no longer be able to read it)
            let retreived_1st_message = Message::find_by_id(john_conn, mid_fromalex.clone().into())
                .expect("Couldn't retreive message as john");
            // Make sure the "from" field is now john
            assert_eq!(Some(uid_john.clone()), retreived_1st_message.from);
        }

        // Try to do the same as john, and find that he's not trustworthy enough
        let fromjohn_fromalex_obj = BuildMessage::new(mid_fromjohn.clone().into())
            .from(uid_alex.clone())
            .finalize();

        assert!(!fromjohn_fromalex_obj.save(alex_conn));
        {
            // Retrieve the message as alex
            let retreived_1st_message = Message::find_by_id(alex_conn, mid_fromjohn.clone().into())
                .expect("Couldn't retreive message as alex");
            // Make sure the "from" field is still john
            assert_eq!(Some(uid_john.clone()), retreived_1st_message.from);
        }
    }

    #[test]
    fn find_all() {
        let db_conn = get_dbconn();

        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 0,
                trustworthyness: 15,
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
                trustworthyness: 5,
            },
        ];

        let uids = User::insert_many(&db_conn.clone().as_princ(Principle::Unauthenticated), users).unwrap();
        let all: Vec<_> = User::find_all(&db_conn.clone().as_princ(Principle::Unauthenticated)).unwrap().iter().map(|obj| obj.id.clone()).collect();
        for id in uids {
            assert!(all.contains(&Some(id)))
        }
    }
}
