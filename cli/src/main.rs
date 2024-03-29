use std::time::Instant;

use clap::{crate_version, App, AppSettings, Arg, SubCommand};

mod commands;
mod project;

fn main() {
    let app = App::new("Schema & Policy Management CLI")
        .version(crate_version!())
        .author("UCSD PLSysSec")
        .setting(AppSettings::ArgRequiredElseHelp)
        .subcommand(
            SubCommand::with_name("init")
                .about("Sets up the migration directory and policy module"),
        )
        .subcommand(
            SubCommand::with_name("new")
                .about("Creates a new migration")
                .arg(Arg::with_name("migration-name"))
                .setting(AppSettings::ArgRequiredElseHelp),
        )
        .subcommand(
            SubCommand::with_name("run")
                .about("Executes a migration on the live database")
                .arg(Arg::with_name("migration-file"))
                .setting(AppSettings::ArgRequiredElseHelp),
        )
        .subcommand(
            SubCommand::with_name("dry-run")
                .about("Produces the policy that results from the migration")
                .arg(Arg::with_name("migration-file"))
                .setting(AppSettings::ArgRequiredElseHelp),
        );

    let matches = app.get_matches();

    match matches.subcommand() {
        ("init", _) => commands::init(),
        ("run", Some(m)) => commands::run(m.value_of("migration-file").unwrap()),
        ("dry-run", Some(m)) => {
            let start = Instant::now();
            commands::dry_run(m.value_of("migration-file").unwrap());
            let end = Instant::now();

            eprintln!("E2E_TIME: {:?}", (end - start).as_micros());
        }
        // Unwrap is safe because ArgRequiredElseHelp
        ("new", Some(m)) => commands::new(m.value_of("migration-name").unwrap()),
        _ => unreachable!("Should never happen on account of ArgRequiredElseHelp"),
    };
}
