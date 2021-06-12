use enforcement::*;

#[path = "../types.rs"]
mod types;
use types::*;

fn main() {
    let db_conn = DBConn::new("localhost", 27017, "BIBIFI-caravan");
    let auth_conn = &db_conn.clone().as_princ(Principal::Unauthenticated);
    let admin_conn = &db_conn.clone().as_princ(Principal::Static("Admin"));
    db_conn.mongo_conn.drop(None).unwrap();
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
    )
    .expect("Couldt not insert post");

    let user_uid = User::insert_one(
        admin_conn,
        user! {
          ident: "djrenren".to_string(),
          password: "password".to_string(),
          salt: "none".to_string(),
          email: "fake@email.com".to_string(),
          created: DateTime::now(),
          admin: true,
          consentForm: POption::None,
          resume: POption::None,
        },
    )
    .expect("Couldn't insert user");

    {
        use POption::{None, Some};
        let user_info_id = UserInformation::insert_one(
            admin_conn,
            userinformation! {
                user: user_uid,
                school: Some("Hard Knocks".into()),
                major: Some("Computers".into()),
                minor: Some("Philosophy".into()),
                degreesHeld: Some("Highschool".into()),
                degree: "Some degree".into(),
                yearsInProgram: Some(4.into()),
                yearsOfExperience: Some(10.into()),
                languages: Some("Ruby Java Spanish".into()),
                favoriteLanguages: Some("Esperanto".into()),
                yearsOfWork: Some(32.into()),
                experienceClass: Some(true),
                experiencePersonal: Some(true),
                experienceInternship: Some(false),
                experienceJob: Some(true),
                securityTraining: None,
                securityExperience: None,
                softwareEngineering: None,
                securityClass: Some(true),
                previousContest: Some(false),
                resumePermission: false,
                age: Some(34),
                nationality: Some("French".into()),
                gender: Some("male".into()),
                agreeToParticipate: false,
                graduationYear: Some(2002),
                programmerRating: Some(10),
                attackerRating: Some(9),
                language: Some("English".into()),
                timezone: None,
            },
        );
    }
}
