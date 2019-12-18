use std::io::{self, Read};
use std::path::Path;

use ::migrate::migrate::migrate;

fn main() {
    // Grab the argument to the binary
    let mut args = std::env::args();
    args.next().expect("Not enough arguments");
    // Arguments are the database name, the policy file, the migration file
    let db_name = args.next().expect("Not enough arguments");
    let policy_file = args.next().expect("Not enough arguments");
    let migration_file = args.next().expect("Not enough arguments");
    // Call the main migration function
    migrate(
        db_name,
        get_contents(Path::new(&policy_file)).expect("Couldn't open policy file"),
        get_contents(Path::new(&migration_file)).expect("Couldn't open migration file"),
    );
}
/// Returns the contents of the file at a given path
///
/// # Arguments
/// * `fname` - The path to the file to read
fn get_contents(fname: &Path) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
}
