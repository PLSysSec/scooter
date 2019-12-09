use policy_lang;

use policy_lang::ir::*;

use std::io::{self, Read};
use std::path::Path;

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
/// Migrate a database, whose schema is outlined in a policy file,
/// using migration commands specified in a migration file.
///
/// # Arguments
///
/// * `db_name` - The name of the database to migrate
///
/// * `policy_text` - The policy-lang source specifying the intial
/// configuration of the database
///
/// * `migration_text` - The migration-lang source specifying the
/// migration
pub fn migrate(db_name: String, policy_text: String, migration_text: String) {
    // Parse the policy text into an ast
    let policy_ast = policy_lang::parse_policy(&policy_text).expect("Couldn't parse policy");
    // Parse the migration text into an ast
    let migration_ast =
        policy_lang::parse_migration(&migration_text).expect("Couldn't parse migration");
    // Extract the type information from th policy ast
    let mut policy_env = extract_types(&policy_ast);
    // Use the type information to lower the policy into ir
    let policy_ir = policy_env.lower(&policy_ast);
    let migration_ir = policy_env.lower_migration(migration_ast);
    // Run the migration
    interpret_migration(db_name, policy_env, migration_ir, policy_ir)
}

#[cfg(test)]
mod tests {
    use super::migrate;
    use mongodb::db::ThreadedDatabase;
    use mongodb::{bson, doc};

    mod types;
    use crate::*;
    use enforcement::*;
    use std::path::Path;
    use types::*;
    #[test]
    fn add_and_remove_fields() {
        // The name of the collection
        let col_name = "User".to_string();
        // Create a connection to the database
        let db_conn = DBConn::new("test");
        // Drop any existing collection by the same name, so that the
        // collection is empty.
        db_conn.mongo_conn.collection(&col_name).drop().unwrap();

        // Two user objects, to be inserted into the database. Note
        // that these users have a "num_followers" field.
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
        // Insert the users into the database, and get back their ids
        let uids = User::insert_many(&db_conn.as_princ(Principle::Public), users).unwrap();
        let (uid_alex, uid_john) = match uids.as_slice() {
            [id1, id2] => (id1, id2),
            _ => panic!("Not the right number of returned ids"),
        };

        // Perform a migration, using the db_name "test", the contents
        // of the policy file, and this migration string. The string
        // removes the num_followers column from the schema.
        migrate(
            "test".to_string(),
            get_contents(
                Path::new(&std::env::current_dir().unwrap())
                    .join("policy.txt".to_string())
                    .as_ref(),
            )
            .unwrap(),
            r#"
                User::RemoveField(num_followers)
                User::AddField(num_friends, I64, u -> 1337)
                User::AddField(num_roomates, I64, u -> 0)
                User::RemoveField(num_roomates)
                "#
            .to_string(),
        );
        // Pull out the resulting docs, using the ids we got when we
        // inserted the originals.
        let alex_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_alex.clone()}), None)
            .unwrap()
            .unwrap();
        let john_result_doc = db_conn
            .mongo_conn
            .collection(&col_name)
            .find_one(Some(doc! {"_id": uid_john.clone()}), None)
            .unwrap()
            .unwrap();

        // Make sure the right things got removed
        assert!(!alex_result_doc.contains_key("num_followers"));
        assert!(!john_result_doc.contains_key("num_followers"));

        assert!(!alex_result_doc.contains_key("num_roomates"));
        assert!(!john_result_doc.contains_key("num_roomates"));

        // Make sure nothing else got removed
        assert_eq!(
            alex_result_doc
                .get_str("username")
                .expect("Couldn't find username key after migration"),
            "Alex"
        );
        assert_eq!(
            john_result_doc
                .get_str("username")
                .expect("Couldn't find username key after migration"),
            "John"
        );
        assert_eq!(
            alex_result_doc
                .get_str("pass_hash")
                .expect("Couldn't find pass_hash key after migration"),
            "alex_hash"
        );
        assert_eq!(
            john_result_doc
                .get_str("pass_hash")
                .expect("Couldn't find pass_hash key after migration"),
            "john_hash"
        );
        assert_eq!(
            alex_result_doc
                .get_i64("num_friends")
                .expect("Couldn't find pass_hash key after migration"),
            1337
        );
        assert_eq!(
            john_result_doc
                .get_i64("num_friends")
                .expect("Couldn't find pass_hash key after migration"),
            1337
        );
    }
}

use mongodb::db::ThreadedDatabase;
use mongodb::{bson, doc};
use mongodb::{Bson, Client, Document, ThreadedClient};
/// Interpret the commands in a migration file, using a given database
/// and policy environment.
///
/// # Arguments
///
/// `db_name` - The name of the database to run the migration on
///
/// `migration_ast` - The parsed migration (a list of migration commands)
///
/// `policy_env` - The type environment on the original policy (pre-migration)
///
/// `policy_ir` - The original policy itself
fn interpret_migration(
    db_name: String,
    env: IrData,
    migration_ir: CompleteMigration,
    policy_ir: CompletePolicy,
) {
    // Create a connection to the database
    let db_conn = Client::connect("localhost", 27017)
        .expect("Failed to initialize client.")
        .db(&db_name);
    // Loop over the migration commands in sequence
    for CompleteMigrationCommand { table, action } in migration_ir.0.into_iter() {
        let policy_collection = &env[table];
        let mongo_collection = db_conn.collection(&policy_collection.name.1);
        let items_old = mongo_collection.find(None, None).unwrap();
        for item in items_old.into_iter() {
            let item = item.unwrap();
            // Get the id of the original item
            let item_id = item.get_object_id("_id").unwrap().clone();
            // Run the commands on this particular item.
            let updated_item = apply_action(item, &action, &env,
                                            &policy_collection, &policy_ir);
            // Replace the old object with the new one in the database
            mongo_collection
                .replace_one(doc! {"_id":item_id}, updated_item, None)
                .expect("Couldn't replace document");
        }
    }
}
/// Apply a list of commands to a single mongo document
///
/// # Arguments
///
/// * `doc` - The mongo document object to operate on
///
/// * `command_list` - A list of actions to perform on this document
///
/// * `policy_collection` - The type and schema information for the
/// current collection
///
/// * `_policy_ir` - The policies on the current collection
fn apply_action(
    doc: Document,
    action: &CompleteMigrationAction,
    env: &IrData,
    policy_collection: &Collection,
    _policy_ir: &CompletePolicy,
) -> Document {
    // Get a mutable document
    let mut result_doc = doc;
    // Apply the command
    match action {
        CompleteMigrationAction::RemoveField { field: field_id } => {
            // Remove the column (and make sure it existed on the object)
            result_doc
                .remove(&policy_collection.field_name(field_id))
                .expect("Couldn't find column to remove in data.");
        }
        CompleteMigrationAction::AddField {
            field: field_id,
            ty: _field_ty,
            init: initializer,
        } => {
            let field_name = policy_collection.field_name(field_id);
            assert!(
                !result_doc.contains_key(&field_name),
                format!(
                    "Document already contained a field with the name \"{}\"",
                    field_name
                )
            );
            result_doc.insert(field_name, exec_query_function(env, initializer, &result_doc));
        }
    };
    result_doc
}

#[derive(Clone)]
pub enum Value {
    Int(i64),
    Float(f64),
    String(String),
}
impl From<Value> for Bson {
    fn from(v: Value) -> Bson {
        match v {
            Value::Int(i) => Bson::I64(i),
            Value::Float(f) => Bson::FloatingPoint(f),
            Value::String(s) => Bson::String(s),
        }
    }
}

struct Evaluator<'a> {
    pub ird: &'a IrData,
}

impl Evaluator<'_> {
    fn new(data: &IrData) -> Evaluator {
        Evaluator{ird: data}
    }
    fn eval_expr(&self, expr_id: &Id<Expr>) -> Value {
        match &self.ird[*expr_id] {
            Expr{id: _, kind: ExprKind::IntConst(i)} => Value::Int(i.clone()),
            Expr{id: _, kind: ExprKind::FloatConst(i)} => Value::Float(i.clone()),
            Expr{id: _, kind: ExprKind::StringConst(i)} => Value::String(i.clone()),
            _ => unimplemented!("Very restricted expr evaluation for now")
        }
    }
}

fn exec_query_function(ir_env: &IrData, f: &Lambda, _arg: &Document) -> Value {
    let evaluator = Evaluator::new(ir_env);
    let Lambda {param: _param, body} = f;
    evaluator.eval_expr(&body)
}
