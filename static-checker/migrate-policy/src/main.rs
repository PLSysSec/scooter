use migrate_policy::*;
use std::env;
use std::path::Path;
fn main() {
    let mut args = std::env::args();
    args.next().expect("Not enough arguments");
    let policy = args.next().expect("Not enough arguments");
    let migration = args.next().expect("Not enough arguments");
    let in_dir = &env::current_dir().expect("Couldn't get current directory");
    let in_path = Path::new(&in_dir);
    let new_policy_text = migrate_policy_from_files(in_path.join(policy).to_str().unwrap(),
                                                    in_path.join(migration).to_str().unwrap());
    println!("{}", new_policy_text);
}
