use migration_lang;
use policy_lang;

use migration_lang::ast::{Command, CommandAction, CommandList};
use policy_lang::ir::*;

use std::collections::HashMap;
use std::io::{self, Read};
use std::path::Path;

fn main() {
    let mut args = std::env::args();
    args.next().expect("Not enough arguments");
    let db_name = args.next().expect("Not enough arguments");
    let policy_file = args.next().expect("Not enough arguments");
    let migration_file = args.next().expect("Not enough arguments");
    migrate(db_name,
            get_contents(Path::new(&policy_file)).expect("Couldn't open policy file"),
            get_contents(Path::new(&migration_file)).expect("Couldn't open migration file"));
}
fn get_contents(fname: &Path) -> io::Result<String> {
    let mut out = String::new();
    std::fs::File::open(fname)?.read_to_string(&mut out)?;
    Ok(out)
}
pub fn migrate(db_name: String, policy_text: String, migration_text: String) {
    let policy_ast = policy_lang::parse_policy(&policy_text)
        .expect("Couldn't parse policy");
    let migration_ast = migration_lang::parse_migration(&migration_text)
        .expect("Couldn't parse migration");
    let mut policy_env = extract_types(&policy_ast);
    let policy_ir = policy_env.lower(&policy_ast);
    interpret_policy(db_name, migration_ast, policy_env, policy_ir)
}

#[cfg(test)]
mod tests {
    use super::migrate;
    use mongodb::db::ThreadedDatabase;
    use mongodb::{bson, doc};

    mod types;
    use types::*;
    use enforcement::*;
    use crate::*;
    use std::path::Path;
    #[test]
    fn remove_num_followers() {
        let db_conn = DBConn::new("test");

        let users: Vec<_> = vec![
            user! {
                username: "Alex".to_string(),
                pass_hash: "alex_hash".to_string(),
                num_followers: "0".to_string(),
            },
            user! {
                username: "John".to_string(),
                pass_hash: "john_hash".to_string(),
                num_followers: "0".to_string(),
            },
        ];
        let col_name = "User".to_string();
        let uids = User::insert_many(&db_conn.as_princ(Principle::Public), users).unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };
        migrate(col_name.clone(),
                get_contents(Path::new(&std::env::current_dir().unwrap())
                             .join("policy.txt".to_string()).as_ref()).unwrap(),
                r#"
                User::RemoveColumn(num_followers)
                "#.to_string());
        let alex_result_doc = db_conn.mongo_conn
            .collection(&col_name)
            .find_one(Some(doc!{"_id": uid_alex.clone()}), None).unwrap().unwrap();
        let john_result_doc = db_conn.mongo_conn
            .collection(&col_name)
            .find_one(Some(doc!{"_id": uid_john.clone()}), None).unwrap().unwrap();

        // Make sure the right thing got removed
        assert!(!alex_result_doc.contains_key("num_followers"));
        assert!(!john_result_doc.contains_key("num_followers"));

        // Make sure nothing else got removed
        assert_eq!(alex_result_doc.get_str("username")
                   .expect("Couldn't find username key after migration"),
                   "Alex");
        assert_eq!(john_result_doc.get_str("username")
                   .expect("Couldn't find username key after migration"),
                   "John");
        assert_eq!(alex_result_doc.get_str("pass_hash")
                   .expect("Couldn't find pass_hash key after migration"),
                   "alex_hash");
        assert_eq!(john_result_doc.get_str("pass_hash")
                   .expect("Couldn't find pass_hash key after migration"),
                   "john_hash");
    }
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
    command_list: &Vec<CommandAction>,
    policy_env: &IrData,
    _policy_ir: &CompletePolicy,
) -> Document {
    let mut result_doc = doc;
    for command in command_list.iter() {
        match command {
            CommandAction::RemoveColumn { col: col_name } => {
                policy_env
                    .collections()
                    .find(|&col| col.name.1 == *col_name)
                    .expect("Couldn't find column to remove in policy.");
                result_doc
                    .remove(col_name)
                    .expect("Couldn't find column to remove in data.");
            }
        };
    }
    result_doc
}
fn group_commandlist_by_collection(cmds: CommandList) -> Vec<(String, Vec<CommandAction>)> {
    let mut col_map: HashMap<String, Vec<CommandAction>> = HashMap::new();
    for command in cmds.0 {
        let Command { table, action } = command;
        match col_map.get_mut(&table) {
            Some(v) => v.push(action),
            None => {
                col_map.insert(table, vec![action]);
            }
        };
    }
    col_map.into_iter().collect()
}
