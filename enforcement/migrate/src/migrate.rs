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
    for cmd in migration_ir.0.into_iter() {
        match cmd {
            CompleteMigrationCommand::CollAction { table, action } =>
                interpret_action(&db_conn, &env, &env[table], action),
            // Creates and deletes actually only operate at the type system level
            CompleteMigrationCommand::Create{..} | CompleteMigrationCommand::Delete{..} =>
            {}
        }
    }
}

fn interpret_action(
    db_conn: &mongodb::db::Database,
    env: &IrData,
    collection: &Collection,
    action: CompleteMigrationAction) {
    match action {
        // Remove field command. Removes a field from all records in the collection.
        CompleteMigrationAction::RemoveField { field } => {
            // Loop over the records
            for item in coll_docs(&db_conn, &collection).into_iter() {
                // Get the item id for replacement
                let item_id = item.get_object_id("_id").unwrap().clone();
                let mut result = item;
                // Remove the field from the mongo doc object
                result.remove(&collection.field_name(&field));
                replace_doc(&db_conn, &collection, item_id, result);
            }
        }
        CompleteMigrationAction::AddField { field, ty: _, init } => {
            for item in coll_docs(&db_conn, &collection).into_iter() {
                let item_id = item.get_object_id("_id").unwrap().clone();
                let mut result = item;
                let field_name = collection.field_name(&field);
                assert!(
                    !result.contains_key(&field_name),
                    format!(
                        "Document already contained a field with the name \"{}\"",
                        field_name
                    )
                );
                result.insert(field_name, exec_query_function(&env, &init, &result));
                replace_doc(&db_conn, &collection, item_id, result);
            }
        }
        CompleteMigrationAction::ChangeField {
            field,
            new_ty: _,
            new_init,
        } => {
            for item in coll_docs(&db_conn, &collection).into_iter() {
                let item_id = item.get_object_id("_id").unwrap().clone();
                let mut result = item;
                let field_name = collection.field_name(&field);
                assert!(
                    result.contains_key(&field_name),
                    format!(
                        "Document doesn't contain a field with the name \"{}\"",
                        field_name
                    )
                );
                result.insert(field_name, exec_query_function(&env, &new_init, &result));
                replace_doc(&db_conn, &collection, item_id, result);
            }
        }
        CompleteMigrationAction::RenameField {
            field_id:_,
            old_name,
            new_name,
        } => {
            for item in coll_docs(&db_conn, &collection).into_iter() {
                let item_id = item.get_object_id("_id").unwrap().clone();
                let mut result = item;
                let field_value = result.remove(&old_name).expect(&format!(
                    "Document doesn't contain a field with the name \"{}\"",
                    old_name
                ));
                assert!(
                    result.insert(new_name.clone(), field_value).is_none(),
                    format!(
                        "Document already contains a field with the name \"{}\"",
                        new_name
                    )
                );
                replace_doc(&db_conn, &collection, item_id, result);
            }
        }
        CompleteMigrationAction::ForEach { param, body } => {
            for item in coll_docs(&db_conn, &collection).into_iter() {
                let mut evaluator = Evaluator::new(&env);
                evaluator.push_scope(&param, Value::Object(item.clone()));
                match body {
                    CompleteObjectCommand::CreateObject { collection, value } => {
                        if let Value::Object(obj) = evaluator.eval_expr(&value) {
                            insert_doc(&db_conn, &env[collection], obj)
                        } else {
                            panic!("Can't insert these kinds of values; typechecking must have failed");
                        }
                    }
                    CompleteObjectCommand::DeleteObject {
                        collection,
                        id_expr,
                    } => {
                        if let Value::Id(id) = evaluator.eval_expr(&id_expr) {
                            delete_doc(&db_conn, &env[collection], id)
                        } else {
                            panic!(
                                "Runtime type error: argument does not evaluate to an id: {:?}",
                                id_expr
                            )
                        }
                    }
                }
            }
        }
    }
}
#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Float(f64),
    String(String),
    Object(Document),
    Id(ObjectId),
}
impl From<Value> for Bson {
    fn from(v: Value) -> Bson {
        match v {
            Value::Int(i) => Bson::I64(i),
            Value::Float(f) => Bson::FloatingPoint(f),
            Value::String(s) => Bson::String(s),
            Value::Object(_) => panic!("Cannot return an object where a value is expected"),
            Value::Id(i) => Bson::ObjectId(i),
        }
    }
}
impl From<Bson> for Value {
    fn from(b: Bson) -> Value {
        match b {
            Bson::I64(i) => Value::Int(i),
            Bson::FloatingPoint(f) => Value::Float(f),
            Bson::String(s) => Value::String(s),
            Bson::ObjectId(i) => Value::Id(i),
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
                let field_name = self.ird[*col_id].field_name(field);
                let normalized_field_name = if field_name == "id" {
                    "_id"
                } else {
                    &field_name
                };

                match obj {
                    Value::Object(d) => d
                        .get(normalized_field_name)
                        .expect("Retrieved value doesn't have the right field")
                        .clone()
                        .into(),
                    _ => panic!("Cannot get fields of non-object values"),
                }
            }
            ExprKind::Object(col_id, fields, template_obj_expr) => {
                let collection = &self.ird[*col_id];
                let mut result_object = doc! {};
                let template_obj_val = template_obj_expr.as_ref().map(|expr| self.eval_expr(expr));
                for (field_name, field_id) in collection.fields() {
                    if field_name == "id" {
                        continue;
                    }
                    let field_value = match fields.iter().find(|(id, _expr)| field_id == id) {
                        Some((_id, expr)) => self.eval_expr(expr),
                        None => match &template_obj_val {
                            Some(Value::Object(template_obj)) => {
                                template_obj.get(field_name).unwrap().clone().into()
                            }
                            Some(_) => panic!("Type system failure: template is not an object"),
                            None => {
                                panic!("Type system failure: couldn't find field {}", field_name)
                            }
                        },
                    };
                    result_object.insert(field_name, field_value);
                }
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
            ExprKind::Var(id) => self
                .lookup(id)
                .expect(&format!("No binding in scope for var {:?}", id)),
            ExprKind::AddI(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(subexpr_l);
                let arg_r = self.eval_expr(subexpr_r);
                if let (Value::Int(i1), Value::Int(i2)) = (arg_l, arg_r) {
                    Value::Int(i1 + i2)
                } else {
                    panic!("Runtime type error: arguments to addi aren't ints");
                }
            }
            ExprKind::AddF(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(subexpr_l);
                let arg_r = self.eval_expr(subexpr_r);
                if let (Value::Float(f1), Value::Float(f2)) = (arg_l, arg_r) {
                    Value::Float(f1 + f2)
                } else {
                    panic!("Runtime type error: arguments to addf aren't floats");
                }
            }
            ExprKind::IntToFloat(subexpr) => {
                let arg = self.eval_expr(subexpr);
                if let Value::Int(i) = arg {
                    Value::Float(i as f64)
                } else {
                    panic!(
                        "Runtime type error: argument to conversion isn't an int {:?}",
                        arg
                    );
                }
            }
            e => unimplemented!("{:?}", e),
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

fn delete_doc(db_conn: &Database, coll: &Collection, id: ObjectId) {
    db_conn
        .collection(&coll.name.1)
        .delete_one(doc! {"_id": id}, None)
        .expect("Couldn't delete document");
}
