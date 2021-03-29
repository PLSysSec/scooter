use crate::login;
use crate::types::*;
use enforcement::{AuthConn, DBCollection, DBConn, Principal, RecordId, TypedRecordId};
use lazy_static::lazy_static;
use rocket::outcome::{IntoOutcome, Outcome};
use rocket::{request, Request};
use serde_json::{from_str, to_string};
use std::collections::HashMap;

pub struct UserId(pub TypedRecordId<User>);
pub struct SessionConn(pub AuthConn);
pub struct AdminConn(pub AuthConn);

lazy_static! {
    static ref DB_CONN: DBConn = DBConn::new("localhost", 27017, "BIBIFI-caravan");
}

impl<'a, 'r> request::FromRequest<'a, 'r> for UserId {
    type Error = !;

    fn from_request(request: &'a request::Request<'r>) -> request::Outcome<UserId, !> {
        request
            .cookies()
            .get_private("user_id")
            .and_then(|cookie| from_str(cookie.value()).ok())
            .map(|id: RecordId| unsafe { UserId(id.ascribe_collection::<User>()) })
            .or_forward(())
    }
}

impl<'a, 'r> request::FromRequest<'a, 'r> for SessionConn {
    type Error = !;

    fn from_request(request: &'a request::Request<'r>) -> request::Outcome<SessionConn, !> {
        Outcome::Success(
            request
                .cookies()
                .get_private("user_id")
                .and_then(|cookie| from_str(cookie.value()).ok())
                .map(|id: RecordId| SessionConn(DB_CONN.clone().as_princ(Principal::Id(id))))
                .unwrap_or_else(|| {
                    SessionConn(DB_CONN.clone().as_princ(Principal::Unauthenticated))
                }),
        )
    }
}

impl<'a, 'r> request::FromRequest<'a, 'r> for AdminConn {
    type Error = !;

    fn from_request(request: &'a request::Request<'r>) -> request::Outcome<AdminConn, !> {
        UserId::from_request(request).and_then(|uid| {
            let db = DB_CONN.clone();
            let conn = db.as_princ(Principal::Id(uid.0.clone().into()));
            User::find_by_id(&conn, uid.0)
                .and_then(|u| u.admin)
                .and_then(|is_admin| {
                    is_admin
                        .then(|| AdminConn(DB_CONN.clone().as_princ(Principal::Static("Admin"))))
                })
                .or_forward(())
        })
    }
}
