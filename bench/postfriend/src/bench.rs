mod types;

use enforcement::*;
use types::*;

use std::env;
use std::fmt;
use std::time::{Duration, Instant};

fn main() {
    let args: Vec<String> = env::args().collect();
    let num_trials = if args.len() > 1 {
        args[1].parse().unwrap()
    } else {
        1000
    };

    let db_conn = get_dbconn("postfriend-bench");
    let main_user_id = setup_db_contents(&db_conn);
    let post_time = time_post(&db_conn, main_user_id.clone(), num_trials);
    println!("Creating a new post: {}", post_time);
    let read_friend_posts_time = time_read_friend_posts(&db_conn, main_user_id, num_trials);

    println!("Reading friends posts: {}", read_friend_posts_time);
}

fn get_dbconn(name: &str) -> DBConn {
    let db_conn = DBConn::new("localhost", 27017, name);
    db_conn.mongo_conn.collection("User").drop(None).ok();
    db_conn.mongo_conn.collection("Post").drop(None).ok();
    db_conn
}

struct TimeEntry {
    pub time_checked: Duration,
    pub time_direct: Duration,
}

impl fmt::Display for TimeEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{:#?} checked, {:#?} direct]",
            self.time_checked, self.time_direct
        )
    }
}

fn setup_db_contents(conn: &DBConn) -> TypedRecordId<User> {
    let users = vec![
        user! {
            username: "bernie".to_string(),
            friends: vec![],
        },
        user! {
            username: "joe".to_string(),
            friends: vec![]
        },
        user! {
            username: "kamala".to_string(),
            friends: vec![]
        },
        user! {
            username: "micheal".to_string(),
            friends: vec![]
        },
    ];

    // Insert the users, and get their ids
    let uids =
        User::insert_many(&conn.clone().as_princ(Principle::Unauthenticated), users).unwrap();
    let (uid_bernie, uid_joe, uid_kamala, uid_micheal) = match uids.as_slice() {
        [id1, id2, id3, id4] => (id1, id2, id3, id4),
        _ => panic!("Not the right number of returned ids"),
    };

    let bernie_conn = conn
        .clone()
        .as_princ(Principle::Id(uid_bernie.clone().into()));
    BuildUser::new(uid_bernie.clone().into())
        .friends(vec![uid_joe.clone(), uid_kamala.clone()])
        .finalize()
        .save(&bernie_conn);

    let kamala_conn = conn
        .clone()
        .as_princ(Principle::Id(uid_kamala.clone().into()));
    BuildUser::new(uid_kamala.clone().into())
        .friends(vec![
            uid_joe.clone(),
            uid_bernie.clone(),
            uid_micheal.clone(),
        ])
        .finalize()
        .save(&kamala_conn);

    let joe_conn = conn.clone().as_princ(Principle::Id(uid_joe.clone().into()));
    BuildUser::new(uid_joe.clone().into())
        .friends(vec![
            uid_kamala.clone(),
            uid_bernie.clone(),
            uid_micheal.clone(),
        ])
        .finalize()
        .save(&joe_conn);

    let micheal_conn = conn
        .clone()
        .as_princ(Principle::Id(uid_micheal.clone().into()));
    BuildUser::new(uid_micheal.clone().into())
        .friends(vec![uid_kamala.clone(), uid_joe.clone()])
        .finalize()
        .save(&micheal_conn);

    let joe_post = post! {
        author: uid_joe.clone(),
        title: "A Message of Unity".to_string(),
        contents: "My fellow americans...".to_string(),
    };
    Post::insert_one(&joe_conn, joe_post);

    let kamala_post = post! {
        author: uid_kamala.clone(),
        title: "Your VPOTUS".to_string(),
        contents: "Ever since I was a little girl...".to_string(),
    };
    Post::insert_one(&kamala_conn, kamala_post);

    let micheal_post = post! {
        author: uid_joe.clone(),
        title: "DNC Funding".to_string(),
        contents: "If you can read this, then I might give you some money... maybe.".to_string(),
    };
    Post::insert_one(&micheal_conn, micheal_post);

    uid_bernie.clone()
}
fn time_post(conn: &DBConn, bernie_id: TypedRecordId<User>, num_trials: u32) -> TimeEntry {
    let bernie_conn = conn
        .clone()
        .as_princ(Principle::Id(bernie_id.clone().into()));
    let before_posting_checked = Instant::now();
    for _ in 0..num_trials {
        Post::insert_one(
            &bernie_conn,
            post! {
                author: bernie_id.clone(),
                title: "I am once again asking for your support".to_string(),
                contents: "It's time for a new generation of leaders...".to_string(),
            },
        );
    }
    let time_taken_checked = (Instant::now() - before_posting_checked) / num_trials;

    TimeEntry {
        time_checked: time_taken_checked,
        time_direct: time_post_unchecked(conn, bernie_id, num_trials),
    }
}
fn time_post_unchecked(conn: &DBConn, bernie_id: TypedRecordId<User>, num_trials: u32) -> Duration {
    use bson::doc;
    let before_posting_unchecked = Instant::now();
    for _ in 0..num_trials {
        conn.mongo_conn
            .collection("Post")
            .insert_one(
                doc! {
                    "author": bernie_id.clone().to_bson(),
                    "title": "I am once again asking for your support".to_string(),
                    "contents": "It's time for a new generation of leaders...".to_string()
                },
                None,
            )
            .unwrap();
    }
    let time_taken_unchecked = (Instant::now() - before_posting_unchecked) / num_trials;
    time_taken_unchecked
}
fn time_read_friend_posts(
    conn: &DBConn,
    bernie_id: TypedRecordId<User>,
    num_trials: u32,
) -> TimeEntry {
    let bernie_conn = conn
        .clone()
        .as_princ(Principle::Id(bernie_id.clone().into()));
    let before_posting_checked = Instant::now();
    for _ in 0..num_trials {
        let bernie_user =
            User::find_by_id(&bernie_conn, bernie_id.clone()).expect("Couldn't get bernie user");
        let friends = bernie_user
            .friends
            .expect("Couldn't get friends of bernie user");
        for friend_id in friends.into_iter() {
            let _friend_posts: Vec<_> = Post::find_full_by_template(
                &bernie_conn,
                BuildPostQuery::new().author(friend_id).finalize(),
            )
            .unwrap()
            .into_iter()
            .map(|post| post.get_contents(&bernie_conn).unwrap().clone())
            .collect();
        }
    }
    let time_taken_checked = (Instant::now() - before_posting_checked) / num_trials;
    TimeEntry {
        time_checked: time_taken_checked,
        time_direct: time_read_friend_posts_unchecked(conn, bernie_id, num_trials),
    }
}
fn time_read_friend_posts_unchecked(
    conn: &DBConn,
    bernie_id: TypedRecordId<User>,
    num_trials: u32,
) -> Duration {
    use bson::doc;
    let before_posting_unchecked = Instant::now();
    for _ in 0..num_trials {
        let user_obj = conn
            .mongo_conn
            .collection("User")
            .find_one(Some(doc! {"_id":bernie_id.clone()}), None)
            .unwrap()
            .unwrap();
        let friends = user_obj.get_array("friends");
        for friend_id in friends.into_iter() {
            let _friend_posts: Vec<_> = conn
                .mongo_conn
                .collection("Post")
                .find(Some(doc! {"author":friend_id}), None)
                .unwrap()
                .filter_map(Result::ok)
                .map(|obj| obj.get_str("contents").unwrap().to_string())
                .collect();
        }
    }
    let time_taken_unchecked = (Instant::now() - before_posting_unchecked) / num_trials;
    time_taken_unchecked
}
