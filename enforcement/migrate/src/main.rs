use migration_lang;
use policy_lang;

use migration_lang::ast::CommandList;
use policy_lang::ir::*;

use std::io::{self, Read};

fn main() {
    let mut args = std::env::args();
    args.next().expect("Not enough arguments.");
    let db_name = args.next().expect("Not enough arguments.");
    let policy_file = args.next().expect("Not enough arguments.");
    let migration_file = args.next().expect("Not enough arguments.");
    let policy_ast =
        policy_lang::parse_policy(&get_contents(policy_file).expect("Couldn't open policy file."))
            .expect("Couldn't parse policy.");
    let migration_ast = migration_lang::parse_migration(
        &get_contents(migration_file).expect("Couldn't open migration file."),
    )
    .expect("Couldn't parse migration.");
    let mut policy_env = extract_types(&policy_ast);
    let policy_ir = policy_env.lower(&policy_ast);
    interpret_policy(db_name, migration_ast, policy_env, policy_ir)
}
fn get_contents(fname: String) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
}

use mongodb::db::ThreadedDatabase;
use mongodb::Client;
use mongodb::Document;
use mongodb::ThreadedClient;
use mongodb::{bson, doc};
fn interpret_policy(
    db_name: String,
    migration_ast: CommandList,
    policy_env: IrData,
    policy_ir: CompletePolicy,
) {
    let collection_groups = group_commandlist_by_collection(migration_ast);
    let db_conn = Client::connect("localhost", 27017)
        .expect("Failed to initialize client.")
        .db(&db_name);

    for (col_name, col_cmds) in collection_groups.into_iter() {
        let mut items_old = db_conn.collection(&col_name).find(None, None).unwrap();
        while items_old.has_next().unwrap() {
            let old_batch = items_old.drain_current_batch().unwrap();
            let new_batch: Vec<Document> = old_batch
                .into_iter()
                .map(|item| apply_commands(item, &col_cmds, &policy_env, &policy_ir))
                .collect();
            for item in new_batch.into_iter() {
                db_conn
                    .collection(&col_name)
                    .replace_one(
                        doc! {"_id":item.get_object_id("_id").unwrap().clone()},
                        item,
                        None,
                    )
                    .expect("Couldn't replace document.");
            }
        }
    }
}
fn apply_commands(
    doc: Document,
    command_list: &CommandList,
    policy_env: &IrData,
    policy_ir: &CompletePolicy,
) -> Document {
    unimplemented!();
}
fn group_commandlist_by_collection(migration_ast: CommandList) -> Vec<(String, CommandList)> {
    unimplemented!();
}
