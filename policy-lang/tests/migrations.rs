use policy_lang::parse_migration;

#[test]
fn simple_valid() {
    let _mig = parse_migration(
        r#"
        User::LoosenCollectionPolicy(create, u -> [u.id])
        User::TightenCollectionPolicy(delete, none)
        User::TightenFieldPolicy(name, read, public)
        User::LoosenFieldPolicy(age, write, a_ -> [])
    "#,
    )
    .unwrap();
}
