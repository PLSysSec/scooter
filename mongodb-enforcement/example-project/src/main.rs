mod types;

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod test {
    use crate::*;
    use enforcement::*;
    use types::*;

    #[test]
    fn insert_then_read() {
        let db_conn = get_dbconn("insert_then_read");

        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 0,
                trustworthyness: 15,
                flair: "".to_string(),
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
                trustworthyness: 5,
                flair: "".to_string(),
            },
        ];

        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let (uid_alex, _uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };

        let authenticator_retrieved_alex = User::find_by_id(
            &db_conn.clone().as_princ(Principal::Static("Authenticator")),
            uid_alex.clone().into(),
        )
        .unwrap();
        let alex_retrieved_alex = User::find_by_id(
            &db_conn
                .clone()
                .as_princ(Principal::Id(uid_alex.clone().into())),
            uid_alex.clone().into(),
        )
        .unwrap();
        let publicly_retrieved_alex = User::find_by_id(
            &db_conn.clone().as_princ(Principal::Unauthenticated),
            uid_alex.clone().into(),
        )
        .unwrap();

        assert_eq!(
            Some("alex_hash".to_string()),
            authenticator_retrieved_alex.pass_hash
        );
        assert_eq!(None, authenticator_retrieved_alex.trustworthyness);
        assert_eq!(None, alex_retrieved_alex.pass_hash);
        assert_eq!(Some(15), alex_retrieved_alex.trustworthyness);
        assert_eq!(None, publicly_retrieved_alex.pass_hash);
    }

    #[test]
    fn set_password() {
        let db_conn = get_dbconn("set_password");
        let alex_id = User::insert_many(
            &db_conn.clone().as_princ(Principal::Unauthenticated),
            vec![user! {username: "Alex".to_string(),
                        pass_hash: "alex_hash".to_string(),
                        num_followers: 0,
                        trustworthyness: 15,
                        flair: "".to_string(),
            }],
        )
        .unwrap()
        .pop()
        .expect("Didn't get any ids back!");

        // Write only the pass hash
        let alex_obj = BuildUser::new(alex_id.clone().into())
            .pass_hash("monster_mash".to_string())
            .finalize();

        assert!(!alex_obj.save(&db_conn.clone().as_princ(Principal::Unauthenticated)));
        {
            let auth_retrieved_alex = User::find_by_id(
                &db_conn.clone().as_princ(Principal::Static("Authenticator")),
                alex_id.clone().into(),
            )
            .unwrap();
            let publicly_retrieved_alex = User::find_by_id(
                &db_conn.clone().as_princ(Principal::Unauthenticated),
                alex_id.clone().into(),
            )
            .unwrap();

            assert_eq!(Some("alex_hash".to_string()), auth_retrieved_alex.pass_hash);
            assert_eq!(None, publicly_retrieved_alex.pass_hash);
        }
        assert!(alex_obj.save(
            &db_conn
                .clone()
                .as_princ(Principal::Id(alex_id.clone().into()))
        ));

        {
            let auth_retrieved_alex = User::find_by_id(
                &db_conn.clone().as_princ(Principal::Static("Authenticator")),
                alex_id.clone().into(),
            )
            .unwrap();
            let publicly_retrieved_alex = User::find_by_id(
                &db_conn.clone().as_princ(Principal::Unauthenticated),
                alex_id.clone().into(),
            )
            .unwrap();

            assert_eq!(
                Some("monster_mash".to_string()),
                auth_retrieved_alex.pass_hash
            );
            assert_eq!(None, publicly_retrieved_alex.pass_hash);
        }
    }

    #[test]
    fn fail_delete_user() {
        let db_conn = get_dbconn("fail_delete_user");

        let alex_id = User::insert_many(
            &db_conn.clone().as_princ(Principal::Unauthenticated),
            vec![user! {username: "Alex".to_string(),
                        pass_hash: "alex_hash".to_string(),
                        num_followers: 0,
                        trustworthyness: 15,
                        flair: "".to_string(),
            }],
        )
        .unwrap()
        .pop()
        .expect("Didn't get any ids back!");

        let result = User::delete_by_id(
            &db_conn
                .clone()
                .as_princ(Principal::Id(alex_id.clone().into())),
            alex_id.clone().into(),
        );
        assert!(!result);
    }

    fn get_dbconn(name: &str) -> DBConn {
        let db_conn = DBConn::new("localhost", 27017, name);
        db_conn.mongo_conn.collection("User").drop(None).ok();
        db_conn.mongo_conn.collection("Message").drop(None).ok();
        db_conn
    }

    #[test]
    fn set_from_trustworthy() {
        let db_conn = get_dbconn("set_from_trustworthy");

        // Add two users, alex and john, where alex has a
        // trustworthyness above ten, and john has one below ten.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 0,
                trustworthyness: 15,
                flair: "".to_string(),
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
                trustworthyness: 5,
                flair: "".to_string(),
            },
        ];

        // Insert the users, and get their ids
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

        // Insert a message from alex to john, and get its id
        let mid_fromalex = Message::insert_one(
            alex_conn,
            message! {
                from: uid_alex.clone(),
                to: uid_john.clone(),
                text: "Hey, how's it hanging dude?".to_string(),
                is_public: false,
            },
        )
        .expect("Couldn't insert message from alex");
        // Insert a message from john to alex, and get its id
        let mid_fromjohn = Message::insert_one(
            john_conn,
            message! {
                from: uid_john.clone(),
                to: uid_alex.clone(),
                text: "Not too bad, how about yourself?".to_string(),
                is_public: false,
            },
        )
        .expect("Couldn't insert message from john");
        // Try to insert a message from john to himself, as alex, and
        // make sure it fails.
        let impersonator_message = message! {
            from: uid_john.clone(),
            to: uid_john.clone(),
            text: "Blah blah blah, I'm a John and I know things".to_string(),
            is_public: false,
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
        let db_conn = get_dbconn("find_all");

        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 0,
                trustworthyness: 15,
                flair: "".to_string(),
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
                trustworthyness: 5,
                flair: "".to_string(),
            },
        ];

        let uids = User::insert_many(&db_conn.clone().as_princ(Principal::Unauthenticated), users)
            .unwrap();
        let all: Vec<_> = User::find_all(&db_conn.clone().as_princ(Principal::Unauthenticated))
            .unwrap()
            .iter()
            .map(|obj| obj.id.clone())
            .collect();
        for id in uids {
            assert!(all.contains(&Some(id)))
        }
    }

    #[test]
    fn read_public_message() {
        let db_conn = get_dbconn("read_public_message");

        // Add three users, alex, john and deian, where alex and deian have a
        // trustworthyness above ten, and john has one below ten.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 0,
                trustworthyness: 15,
                flair: "".to_string(),
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
                trustworthyness: 5,
                flair: "".to_string(),
            },
            user! {
                username: "Deian".to_string(),
                pass_hash: "deian_hash".to_string(),
                num_followers: 100,
                trustworthyness: 0,
                flair: "".to_string(),
            },
        ];

        let unauthenticated_conn = &db_conn.clone().as_princ(Principal::Unauthenticated);
        // Insert the users, and get their ids
        let uids = User::insert_many(unauthenticated_conn, users).unwrap();
        let (uid_alex, uid_john, uid_deian) = match uids.as_slice() {
            [id1, id2, id3] => (id1, id2, id3),
            _ => panic!("Not the right number of returned ids"),
        };
        // Make connection objects for all users
        let alex_conn = &db_conn
            .clone()
            .as_princ(Principal::Id(uid_alex.clone().into()));
        let _john_conn = &db_conn
            .clone()
            .as_princ(Principal::Id(uid_john.clone().into()));
        let deian_conn = &db_conn
            .clone()
            .as_princ(Principal::Id(uid_deian.clone().into()));

        // Insert a message from alex to john, and get its id
        let mid_public_update = Message::insert_one(
            alex_conn,
            message! {
                from: uid_alex.clone(),
                to: uid_john.clone(),
                text: "Update: I wrote a test for `public` appearing in IR Exprs!".to_string(),
                is_public: true,
            },
        )
        .expect("Couldn't insert message from alex");
        // Retrieve the message as john (alex should no longer be able to read it)
        let retreived_as_deian_message =
            Message::find_by_id(deian_conn, mid_public_update.clone().into())
                .expect("Couldn't retreive message as deian");
        // Make sure the message text is readable
        assert!(retreived_as_deian_message.text.is_some());
        // Retrieve the message as john (alex should no longer be able to read it)
        let retreived_as_unauth_message =
            Message::find_by_id(unauthenticated_conn, mid_public_update.clone().into())
                .expect("Couldn't retreive message as unauthenticated");
        // Make sure the message text is readable
        assert!(retreived_as_unauth_message.text.is_some());
    }

    #[test]
    fn read_flair() {
        let db_conn = get_dbconn("read_flair");

        // Add three users, alex, john and deian, where alex and deian have a
        // trustworthyness above ten, and john has one below ten.
        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: 0,
                trustworthyness: 15,
                flair: "".to_string(),
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: 0,
                trustworthyness: 5,
                flair: "I'm secretly incredible at massage".to_string(),
            },
            user! {
                username: "Deian".to_string(),
                pass_hash: "deian_hash".to_string(),
                num_followers: 100,
                trustworthyness: 0,
                flair: "".to_string(),
            },
        ];
        let unauthenticated_conn = &db_conn.clone().as_princ(Principal::Unauthenticated);
        // Insert the users, and get their ids
        let uids = User::insert_many(unauthenticated_conn, users).unwrap();
        let (uid_alex, uid_john, uid_deian) = match uids.as_slice() {
            [id1, id2, id3] => (id1, id2, id3),
            _ => panic!("Not the right number of returned ids"),
        };
        // Make connection objects for all users
        let alex_conn = &db_conn
            .clone()
            .as_princ(Principal::Id(uid_alex.clone().into()));
        let _john_conn = &db_conn
            .clone()
            .as_princ(Principal::Id(uid_john.clone().into()));
        let deian_conn = &db_conn
            .clone()
            .as_princ(Principal::Id(uid_deian.clone().into()));
        // Insert a multi message from deian to alex and john, and get its id
        let _meeting_message = MultiMessage::insert_one(
            deian_conn,
            multimessage! {
                from: uid_deian.clone(),
                to: vec![uid_john.clone(), uid_alex.clone()],
                text: "Are we still meeting today?".to_string(),
            },
        )
        .expect("Couldn't insert message from alex");

        let retrieved_as_alex_john = User::find_by_id(alex_conn, uid_john.clone().into())
            .expect("Couldn't retreive john as alex");
        assert_eq!(
            retrieved_as_alex_john.flair,
            Some("I'm secretly incredible at massage".to_string())
        );

        let retrieved_as_deian_john = User::find_by_id(deian_conn, uid_john.clone().into())
            .expect("Couldn't retreive john as deian");
        assert_eq!(retrieved_as_deian_john.flair, None);
    }
}
