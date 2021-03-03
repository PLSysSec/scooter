use policy_lang::parse_migration;

#[test]
fn simple_valid() {
    let _mig = parse_migration(
        r#"
        User::WeakenPolicy(create, u -> [u.id])
        User::UpdatePolicy(delete, none)
        User::UpdateFieldPolicy(name, read, public)
        User::WeakenFieldPolicy(age, write, a_ -> [])
    "#,
    )
    .unwrap();
}
