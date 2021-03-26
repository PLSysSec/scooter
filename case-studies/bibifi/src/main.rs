#![feature(proc_macro_hygiene, decl_macro, never_type)]
use std::collections::HashMap;

mod types;
mod session;
use session::*;

use rocket_contrib::templates::Template;
use serde::Serialize;

use enforcement::*;
use types::*;

#[macro_use]
extern crate rocket;

#[derive(Serialize)]
struct AnnouncedDate {
    name: String,
    start_str: String,
    end_str: String,
}

#[derive(Serialize)]
struct AnnouncedPost {
    title: String,
    timestamp_str: String,
    content: String,
}

#[derive(Serialize)]
struct Context {
    dates: Vec<AnnouncedDate>,
    posts: Vec<AnnouncedPost>,
}

#[get("/")]
fn index() -> &'static str {
    "This page doesn't exist"
}

#[get("/announcements")]
fn announcements(conn: SessionConn) -> Template {
    let SessionConn(ref auth_conn) = conn;
    let all_contests = Contest::find_all(auth_conn);
    let most_recent_contest: PartialContest = all_contests
        .expect("Can't get contests!")
        .into_iter()
        .max_by_key(|contest| {
            contest
                .buildStart
                .as_ref()
                .expect("Cannot access buildstart on contests!")
                .clone()
        })
        .expect("No contests in DB");
    let buildStart = most_recent_contest.buildStart.as_ref().unwrap().clone();
    let buildEnd = most_recent_contest.buildEnd.as_ref().unwrap().clone();
    let breakFixStart = most_recent_contest.breakFixStart.as_ref().unwrap().clone();
    let breakEnd = most_recent_contest.breakEnd.as_ref().unwrap().clone();
    let fixEnd = most_recent_contest.fixEnd.as_ref().unwrap().clone();
    let dates = vec![
        AnnouncedDate {
            name: "Build It Round".to_string(),
            start_str: buildStart.to_string(),
            end_str: buildEnd.to_string(),
        },
        AnnouncedDate {
            name: "Break It Round".to_string(),
            start_str: breakFixStart.to_string(),
            end_str: breakEnd.to_string(),
        },
        AnnouncedDate {
            name: "Fix It Round".to_string(),
            start_str: breakFixStart.to_string(),
            end_str: fixEnd.to_string(),
        },
    ];
    let contest_posts = Post::find_full_by_template(
        auth_conn,
        BuildPostQuery::new()
            .contest(most_recent_contest.id.as_ref().unwrap().clone())
            .finalize(),
    )
    .expect("Couldn't get posts");

    let posts: Vec<AnnouncedPost> = contest_posts
        .into_iter()
        .filter(|post| !**post.get_draft(auth_conn).as_ref().unwrap())
        .map(|post| AnnouncedPost {
            title: post.get_title(auth_conn).as_ref().unwrap().to_string(),
            timestamp_str: post.get_timestamp(auth_conn).as_ref().unwrap().to_string(),
            content: post.get_content(auth_conn).as_ref().unwrap().to_string(),
        })
        .collect();

    Template::render(
        "announcements",
        Context {
            dates: dates,
            posts: posts,
        },
    )
}

#[get("/profile/account")]
fn profile_account(user: UserId) -> Template {
    Template::render(
        "profile",
        HashMap::<(), ()>::new(),
    )
}

#[catch(404)]
fn not_found(req: &rocket::request::Request) -> String {
    format!("I couldn't find '{}'. Try something else?", req.uri())
}

fn setup_db() {
    let db_conn = DBConn::new("localhost", 27017, "BIBIFI-caravan");
    let auth_conn = &db_conn.clone().as_princ(Principal::Unauthenticated);
    let admin_conn = &db_conn.clone().as_princ(Principal::Static("Admin"));
    db_conn.mongo_conn.collection("Contest").drop(None).ok();
    db_conn.mongo_conn.collection("Post").drop(None).ok();
    let contest_uid = Contest::insert_one(
        auth_conn,
        contest! {
            url: "".to_string(),
            title: "caravan-contest".to_string(),
            buildStart: DateTime::now(),
            buildEnd: DateTime::now(),
            breakFixStart: DateTime::now(),
            breakEnd: DateTime::now(),
            fixEnd: DateTime::now(),
            dependencies: vec![],
        },
    )
    .expect("Could not insert contest!");
    let post_uid = Post::insert_one(
        admin_conn,
        post! {
            title: "This is a test post!".to_string(),
            contest: contest_uid,
            timestamp: DateTime::now(),
            draft: false,
            content: "This post is retrieved from the database using Scooter".to_string(),
            markdown: "".to_string(),
        },
    ).expect("Couldt not insert post");
}

fn main() {
    setup_db();
    rocket::ignite()
        .mount("/", routes![index, announcements, profile_account])
        .register(catchers![not_found])
        .attach(Template::fairing())
        .launch();
}
