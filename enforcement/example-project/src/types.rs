use enforcement::*;

#[collection(policy_module="user_policies")]
pub struct User {
    pub pass_hash: String,
    pub username: String,
}

mod user_policies {
    use super::*;
    pub fn pass_hash(r: &User) -> PolicyValue {
        PolicyValue::Ids(r.id.iter().cloned().collect())
    }
    pub fn username(_: &User) -> PolicyValue {
        PolicyValue::Public
    }
}

