use std::process::exit;

use crate::project::Project;

pub fn init() {
    //  let root = find_root().unwrap();
    //    add_enforcement_dependency(root.join("Cargo.toml"));
}

pub fn new(migration_name: &str) {
    let proj = Project::find_from_cwd().unwrap();
    proj.create_migration(migration_name).unwrap();
}

pub fn run(migration_path: &str) {
    let proj = Project::find_from_cwd().expect("Couln't find the current project");
    match proj.run_migration(migration_path) {
        Err(e) => {
            eprintln!("Couldn't run the migration. {}", e);
            exit(1)
        }
        _ => {}
    }
    println!("Migration successful");
}

pub fn dry_run(migration_path: &str) {
    let proj = Project::find_from_cwd().unwrap();
    match proj.dry_run_migration(migration_path) {
        Err(e) => {
            eprintln!("Couldn't run the migration. {}", e);
            exit(1)
        }
        Ok(new_policy) => {
            println!("{}", new_policy);
        }
    }
}
