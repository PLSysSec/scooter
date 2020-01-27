
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
    let proj = Project::find_from_cwd().unwrap();
    proj.run_migration(migration_path).unwrap();
    println!("Migration successful");
}

pub fn dry_run(migration_path: &str) {
    let proj = Project::find_from_cwd().unwrap();
    let new_policy = proj.dry_run_migration(migration_path);
    println!("{}", new_policy);
}