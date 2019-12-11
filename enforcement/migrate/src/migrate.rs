use policy_lang;

use policy_lang::ir::*;

use mongodb::db::{Database, ThreadedDatabase};
use mongodb::oid::ObjectId;
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
    _policy_ir: CompletePolicy,
) {
    // Create a connection to the database
    let db_conn = Client::connect("localhost", 27017)
        .expect("Failed to initialize client.")
        .db(&db_name);
    // Loop over the migration commands in sequence
    for CompleteMigrationCommand { table, action } in migration_ir.0.into_iter() {
        let policy_collection = &env[table];
        match action {
            CompleteMigrationAction::RemoveField { field } => {
                for item in coll_docs(&db_conn, &policy_collection).into_iter() {
                    let item_id = item.get_object_id("_id").unwrap().clone();
                    let mut result = item;
                    result.remove(&policy_collection.field_name(&field));
                    replace_doc(&db_conn, &policy_collection, item_id, result);
                }
            }
            CompleteMigrationAction::AddField { field, ty: _, init } => {
                for item in coll_docs(&db_conn, &policy_collection).into_iter() {
                    let item_id = item.get_object_id("_id").unwrap().clone();
                    let mut result = item;
                    let field_name = policy_collection.field_name(&field);
                    assert!(
                        !result.contains_key(&field_name),
                        format!(
                            "Document already contained a field with the name \"{}\"",
                            field_name
                        )
                    );
                    result.insert(field_name, exec_query_function(&env, &init, &result));
                    replace_doc(&db_conn, &policy_collection, item_id, result);
                }
            }
            CompleteMigrationAction::ForEach { param, body } => {
                for item in coll_docs(&db_conn, &policy_collection).into_iter() {
                    match body {
                        CompleteObjectCommand::CreateObject { collection, value } => {
                            let mut evaluator = Evaluator::new(&env);
                            evaluator.push_scope(&param, Value::Object(item.clone()));
                            let result = evaluator.eval_expr(&value);
                            match result {
                                Value::Object(doc) => insert_doc(&db_conn, &env[collection], doc),
                                _ => panic!("Can't insert these kinds of values; typechecking must have failed"),
                            };
                        }
                    }
                }
            }
        }
    }
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
            Bson::String(s) => Value::String(s),
            _ => panic!("These kinds of bson objects shouldn't exist"),
        }
    }
}

struct Evaluator<'a> {
    pub ird: &'a IrData,
    env: Vec<(Id<Def>, Value)>,
}

impl Evaluator<'_> {
    fn new(data: &IrData) -> Evaluator {
        Evaluator {
            ird: data,
            env: vec![],
        }
    }
    fn push_scope(&mut self, id: &Id<Def>, val: Value) {
        self.env.push((id.clone(), val));
    }
    fn pop_scope(&mut self, id: &Id<Def>) {
        assert_eq!(self.env.pop().unwrap().0, *id);
    }
    fn lookup(&self, target_id: &Id<Def>) -> Option<Value> {
        for (var_id, var_val) in self.env.iter() {
            if var_id == target_id {
                return Some((*var_val).clone());
            }
        }
        None
    }
    fn eval_expr(&self, expr_id: &Id<Expr>) -> Value {
        match &self.ird[*expr_id].kind {
            ExprKind::IntConst(i) => Value::Int(i.clone()),
            ExprKind::FloatConst(f) => Value::Float(f.clone()),
            ExprKind::StringConst(s) => Value::String(s.clone()),
            ExprKind::Path(col_id, var, field) => {
                let obj = self
                    .lookup(var)
                    .expect("Couldn't find a value in scope for identifier");
                match obj {
                    Value::Object(d) => d
                        .get(&self.ird[*col_id].field_name(field))
                        .expect("Retrieved value doesn't have the right field")
                        .clone()
                        .into(),
                    _ => panic!("Cannot get fields of non-object values"),
                }
            }
            ExprKind::Object(col_id, fields) => {
                let collection = &self.ird[*col_id];
                let mut result_object = doc! {};
                for (field_id, field_value) in fields.iter() {
                    result_object
                        .insert(collection.field_name(field_id), self.eval_expr(field_value));
                }
                Value::Object(result_object)
            }
            ExprKind::Append(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(subexpr_l);
                let arg_r = self.eval_expr(subexpr_r);
                if let (Value::String(s1), Value::String(s2)) = (arg_l, arg_r) {
                    Value::String(s1 + &s2)
                } else {
                    panic!("Arguments to append aren't strings at runtime! Type system failure");
                }
            }
            _ => unimplemented!("Very restricted expr evaluation for now"),
        }
    }
}

fn exec_query_function(ir_env: &IrData, f: &Lambda, arg: &Document) -> Value {
    let mut evaluator = Evaluator::new(ir_env);
    let Lambda { param, body } = f;
    evaluator.push_scope(param, Value::Object(arg.clone()));
    let result = evaluator.eval_expr(&body);
    evaluator.pop_scope(param);
    result
}

fn coll_docs(db_conn: &Database, coll: &Collection) -> Vec<Document> {
    db_conn
        .collection(&coll.name.1)
        .find(None, None)
        .unwrap()
        .into_iter()
        .map(|d| d.unwrap())
        .collect()
}
fn replace_doc(db_conn: &Database, coll: &Collection, id: ObjectId, new: Document) {
    db_conn
        .collection(&coll.name.1)
        .replace_one(doc! {"_id": id}, new, None)
        .expect("Couldn't replace document");
}

fn insert_doc(db_conn: &Database, coll: &Collection, new: Document) {
    db_conn
        .collection(&coll.name.1)
        .insert_one(new, None)
        .expect("Couldn't insert document");
}
