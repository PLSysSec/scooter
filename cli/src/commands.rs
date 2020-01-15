
use crate::project::Project;

pub fn init() {
  //  let root = find_root().unwrap();
//    add_enforcement_dependency(root.join("Cargo.toml"));

}

pub fn new(migration_name: &str) {
    let proj = Project::find_from_cwd().unwrap();
    proj.create_migration(migration_name);
}
