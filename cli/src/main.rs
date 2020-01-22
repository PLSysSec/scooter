use clap::{Arg, App, SubCommand, crate_version, AppSettings};

mod commands;
mod project;

fn main() {
    let app = App::new("Schema & Policy Management CLI")
        .version(crate_version!())
        .author("UCSD PLSysSec")
        .setting(AppSettings::ArgRequiredElseHelp)
        .subcommand(SubCommand::with_name("init")
            .about("Sets up the migration directory and policy module"))
        .subcommand(SubCommand::with_name("new")
            .about("Creates a new migration")
            .arg(Arg::with_name("migration-name"))
            .setting(AppSettings::ArgRequiredElseHelp))
        .subcommand(SubCommand::with_name("run")
            .about("Executes a migration on the live database")
            .arg(Arg::with_name("migration-file")))
        .subcommand(SubCommand::with_name("dry-run")
            .about("Produces the policy that results from the migration")
            .arg(Arg::with_name("migration-file")));

    let matches = app.get_matches();

    match matches.subcommand() {
        ("init", _) => commands::init(),
        ("run", Some(m)) => commands::run(m.value_of("migration-file").unwrap()),
        ("dry-run", Some(m)) => commands::dry_run(m.value_of("migration-file").unwrap()),
        // Unwrap is safe because ArgRequiredElseHelp
        ("new", Some(m)) => commands::new(m.value_of("migration-name").unwrap()),
        _ => { 
            unreachable!("Should never happen on account of ArgRequiredElseHelp")
        }
    };
}
