use policy_lang;

use policy_lang::ir::*;

use mongodb::db::ThreadedDatabase;
use mongodb::{bson, doc};
use mongodb::{Bson, Client, Document, ThreadedClient};

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
            let updated_item = apply_action(item, &action, &env, &policy_collection, &policy_ir);
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
            result_doc.insert(
                field_name,
                exec_query_function(env, initializer, &result_doc),
            );
        }
    };
    result_doc
}

#[derive(Clone)]
pub enum Value {
    Int(i64),
    Float(f64),
    String(String),
    Object(Document),
}
impl From<Value> for Bson {
    fn from(v: Value) -> Bson {
        match v {
            Value::Int(i) => Bson::I64(i),
            Value::Float(f) => Bson::FloatingPoint(f),
            Value::String(s) => Bson::String(s),
            Value::Object(_) => panic!("Cannot return an object where a value is expected"),
        }
    }
}
impl From<Bson> for Value {
    fn from(b: Bson) -> Value {
        match b {
            Bson::I64(i) => Value::Int(i),
            Bson::FloatingPoint(f) => Value::Float(f),
            Bson::String(s) => Bson::String(s),
            _ => panic!("These kinds of bson objects shouldn't exist")
        }
    }
}

struct Evaluator<'a> {
    pub ird: &'a IrData,
}

impl Evaluator<'_> {
    fn new(data: &IrData) -> Evaluator {
        Evaluator { ird: data }
    }
    fn eval_expr(&self, expr_id: &Id<Expr>) -> Value {
        match &self.ird[*expr_id].kind {
            ExprKind::IntConst(i) => Value::Int(i.clone()),
            ExprKind::FloatConst(f) => Value::Float(f.clone()),
            ExprKind::StringConst(s) => Value::String(s.clone()),
            _ => unimplemented!("Very restricted expr evaluation for now"),
        }
    }
}

fn exec_query_function(ir_env: &IrData, f: &Lambda, _arg: &Document) -> Value {
    let evaluator = Evaluator::new(ir_env);
    let Lambda {
        param: _param,
        body,
    } = f;
    evaluator.eval_expr(&body)
}
