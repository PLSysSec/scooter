#![feature(proc_macro_hygiene, decl_macro)]
#[macro_use]
extern crate rocket;

use chrono::DateTime;

use rocket_contrib::templates::Template;
use serde::Serialize;

use enforcement::*;
use types::*;


#[derive(Serialize)]
struct Context {
    contest: Contest,
}

#[get("/")]
fn index() -> &'static str {
    "Hello, world!"
}

#[get("/announcements")]
fn announcements() -> Template {
    let db_conn = DBConn::new("localhost", 27017, "BIBIFI-caravan");
    Template::render("announcements", Context {})
}

fn setup_db() {
    let db_conn = DBConn::new("localhost", 27017, "BIBIFI-caravan");
    db_conn.mongo_conn.collection("Contest").drop(None).ok();
    db_conn.mongo_conn.collection("Post").drop(None).ok();
    let contest_uid = Contest::insert_one(
        &db_conn.clone().as_princ(Principle::Unauthenticated),
        contest! {
            url: "".to_string(),
            title: "caravan-contest".to_string(),
            buildStart: Local::now(),
            buildEnd: Local::now(),
            breakFixStart: Local::now(),
            breakEnd: Local::now(),
            fixEnd: Local::now(),
        },
    );
}

fn main() {
    setup_db();
    rocket::ignite()
        .mount("/", routes![index, announcements])
        .attach(Template::fairing())
        .launch();
}
