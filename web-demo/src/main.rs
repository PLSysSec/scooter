use rocket::{
    form::{Form, FromForm},
    fs::{relative, FileServer},
    launch, post, routes,
    serde::Deserialize,
};
use static_checker::migrate::migrate_policy;

#[derive(Debug, Clone, FromForm, Deserialize)]
#[serde(crate = "rocket::serde")]
struct MigrationMessage {
    pub policy: String,
    pub migration: String,
}

#[post("/run_migration", data = "<form>")]
fn hello(form: Form<MigrationMessage>) -> String {
    let msg = form.into_inner();
    match migrate_policy(&msg.policy, &msg.migration) {
        Ok(policy) => policy,
        Err(err) => err.to_string(),
    }
}

#[launch]
fn rocket() -> _ {
    rocket::build()
        .mount("/", routes![hello])
        .mount("/", FileServer::from(relative!("static")))
}
