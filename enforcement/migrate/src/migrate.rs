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
            CompleteMigrationCommand::CollAction { table, action } => {
                interpret_action(&db_conn, &env, &env[table], action)
            }
            // Creates and deletes actually only operate at the type system level
            CompleteMigrationCommand::Create { .. } | CompleteMigrationCommand::Delete { .. } => {}
        }
    }
}

// Run a single migration action on a table
fn interpret_action(
    db_conn: &mongodb::db::Database,
    env: &IrData,
    collection: &Collection,
    action: CompleteMigrationAction,
) {
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
        // Add a field to all records in the collection
        CompleteMigrationAction::AddField { field, ty: _, init } => {
            // Loop over the records
            for item in coll_docs(&db_conn, &collection).into_iter() {
                // Get the item id for replacement
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
                // Inser the field into the object
                result.insert(field_name, exec_query_function(&env, &init, &result));
                replace_doc(&db_conn, &collection, item_id, result);
            }
        }
        // Change the value and type of a field, but not its name.
        CompleteMigrationAction::ChangeField {
            field,
            new_ty: _,
            new_init,
        } => {
            // Loop over the records
            for item in coll_docs(&db_conn, &collection).into_iter() {
                // Get the object
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
                // Insert the new field value into the object. Note
                // that here, we don't have to worry about changing
                // the type, as that is handled entirely at the
                // IR/typechecking level.
                result.insert(field_name, exec_query_function(&env, &new_init, &result));
                replace_doc(&db_conn, &collection, item_id, result);
            }
        }
        // Change the name of a field, but not its value or type. Note
        // that Coll::RenameField(field, new_name) is semantically
        // equivalent to Coll::Addfield(new_name, old_type, x ->
        // x.field) followed by Coll::DeleteField(field)
        CompleteMigrationAction::RenameField {
            field_id: _,
            old_name,
            new_name,
        } => {
            // Loop over the records
            for item in coll_docs(&db_conn, &collection).into_iter() {
                let item_id = item.get_object_id("_id").unwrap().clone();
                let mut result = item;
                // Remove the old field, and get its value.
                let field_value = result.remove(&old_name).expect(&format!(
                    "Document doesn't contain a field with the name \"{}\"",
                    old_name
                ));
                // Insert the new field, making sure there didn't
                // already exist a field with that name.
                assert!(
                    result.insert(new_name.clone(), field_value).is_none(),
                    format!(
                        "Document already contains a field with the name \"{}\"",
                        new_name
                    )
                );
                // Replace the document
                replace_doc(&db_conn, &collection, item_id, result);
            }
        }
        // Run an object command for every item in a collection.
        CompleteMigrationAction::ForEach { param, body } => {
            // Set the evaluator for expressions under this binder
            let mut evaluator = Evaluator::new(&env);
            for item in coll_docs(&db_conn, &collection).into_iter() {
                // Push the document parameter to the variable stack
                evaluator.push_scope(&param, Value::Object(item.clone()));
                match body {
                    // Add a new object to a given collection.
                    CompleteObjectCommand::CreateObject { collection, value } => {
                        // Evaluate the object expression, and make
                        // sure it's an Object value.
                        if let Value::Object(obj) = evaluator.eval_expr(&value) {
                            // Static checking should ensure that it's
                            // the right kind of object (has all the
                            // fields), so we're not going to check
                            // that here.
                            insert_doc(&db_conn, &env[collection], obj)
                        } else {
                            // If it's not, something must have gone
                            // wrong with static checking.
                            panic!(
                                "Can't insert these kinds of values; typechecking must have failed"
                            );
                        }
                    }
                    // Delete an object from a collectino by it's id.
                    CompleteObjectCommand::DeleteObject {
                        collection,
                        id_expr,
                    } => {
                        // Make sure the id expression evaluates to an id value
                        if let Value::Id(id) = evaluator.eval_expr(&id_expr) {
                            // Delete the document
                            delete_doc(&db_conn, &env[collection], id)
                        } else {
                            // If it doesn't evaluate to an ID,
                            // something must have gone wrong in type
                            // checking.
                            panic!(
                                "Runtime type error: argument does not evaluate to an id: {:?}",
                                id_expr
                            )
                        }
                    }
                }
                // Pop the document off the variable stack
                evaluator.pop_scope(&param);
            }
        }
    }
}

/// Possible value types in our languages
#[derive(Clone, Debug)]
pub enum Value {
    /// Primitive integers
    Int(i64),
    /// Primitive floats
    Float(f64),
    /// Primitive strings
    String(String),
    /// Object values. They are represented by the MongoDocument type,
    /// but not all valid MongoDocuments contain valid values, so be
    /// careful.
    Object(Document),
    /// An object ID in the database.
    Id(ObjectId),
    /// A list of possibly heterogenous values
    List(Vec<Value>),
}
//  Converts our values to bson and back. Currently only operates on
//  primitives, ids, and lists; object values are assumed not to need
//  this.
impl From<Value> for Bson {
    fn from(v: Value) -> Bson {
        match v {
            Value::Int(i) => Bson::I64(i),
            Value::Float(f) => Bson::FloatingPoint(f),
            Value::String(s) => Bson::String(s),
            Value::Object(_) => panic!("Cannot return an object where a value is expected"),
            Value::Id(i) => Bson::ObjectId(i),
            Value::List(vs) => Bson::Array(vs.iter().map(|v| v.clone().into()).collect()),
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

// A naming environment and value context for evaluating expressinos.
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
    // Push a variable into scope with a value
    fn push_scope(&mut self, id: &Id<Def>, val: Value) {
        self.env.push((id.clone(), val));
    }
    // Pop the last variable from scope. This takes an identifier
    // again, to make sure you're not popping someone elses variable,
    // but you still need to treat it like a stack.
    fn pop_scope(&mut self, id: &Id<Def>) {
        assert_eq!(self.env.pop().unwrap().0, *id);
    }
    // Lookup a variable definition in the definition map.
    fn lookup(&self, target_id: &Id<Def>) -> Option<Value> {
        for (var_id, var_val) in self.env.iter() {
            if var_id == target_id {
                return Some((*var_val).clone());
            }
        }
        None
    }
    // Evaluate an expression down to a value
    fn eval_expr(&self, expr_id: &Id<Expr>) -> Value {
        match &self.ird[*expr_id].kind {
            // Constants evaluate to the constant value
            ExprKind::IntConst(i) => Value::Int(i.clone()),
            ExprKind::FloatConst(f) => Value::Float(f.clone()),
            ExprKind::StringConst(s) => Value::String(s.clone()),
            // Paths are field lookups on an object.
            ExprKind::Path(col_id, var, field) => {
                // Look up the object
                let obj = self
                    .lookup(var)
                    .expect("Couldn't find a value in scope for identifier");
                // Get the string name of the field, using the col_id
                // that the typechecker put in.
                let field_name = self.ird[*col_id].field_name(field);
                // If the field name is "id", then translate it to
                // "_id" for the mongo calls.
                let normalized_field_name = if field_name == "id" {
                    "_id"
                } else {
                    &field_name
                };

                // Get the field value.
                match obj {
                    Value::Object(d) => d
                        .get(normalized_field_name)
                        .expect("Retrieved value doesn't have the right field")
                        .clone()
                        .into(),
                    _ => panic!("Cannot get fields of non-object values"),
                }
            }
            // An object spefifier, like User { username: "Alex", ...u}
            ExprKind::Object(col_id, fields, template_obj_expr) => {
                let collection = &self.ird[*col_id];
                let mut result_object = doc! {};
                // If there's a template value expression, evaluate
                // it.
                let template_obj_val = template_obj_expr.as_ref().map(|expr| self.eval_expr(expr));
                for (field_name, field_id) in collection.fields() {
                    // We don't need to directly propogate the id, as
                    // it'll be assigned by mongo when we add to the
                    // database.
                    if field_name == "id" {
                        continue;
                    }
                    // Lookup the field value in the fields specified.
                    let field_value = match fields.iter().find(|(id, _expr)| field_id == id) {
                        // If we find it, evaluate the expression
                        // given, and use it's value for the field.
                        Some((_id, expr)) => self.eval_expr(expr),
                        // Otherwise, use the value from the template
                        // object value.
                        None => match &template_obj_val {
                            Some(Value::Object(template_obj)) => {
                                // Get the field from the object.
                                template_obj.get(field_name).unwrap().clone().into()
                            }
                            // The type system should prevent these
                            // cases.
                            Some(_) => panic!("Type system failure: template is not an object"),
                            None => {
                                panic!("Type system failure: couldn't find field {}", field_name)
                            }
                        },
                    };
                    // Finally, insert the field and it's value into
                    // the object.
                    result_object.insert(field_name, field_value);
                }
                Value::Object(result_object)
            }
            // String append
            ExprKind::AppendS(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(subexpr_l);
                let arg_r = self.eval_expr(subexpr_r);
                if let (Value::String(s1), Value::String(s2)) = (arg_l, arg_r) {
                    Value::String(s1 + &s2)
                } else {
                    panic!("Arguments to append aren't strings at runtime! Type system failure");
                }
            }
            // List append
            ExprKind::AppendL(_ty, subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(subexpr_l);
                let arg_r = self.eval_expr(subexpr_r);
                if let (Value::List(s1), Value::List(s2)) = (arg_l, arg_r) {
                    let mut result = s1.clone();
                    result.append(&mut s2.clone());
                    Value::List(result)
                } else {
                    panic!("Arguments to append aren't strings at runtime! Type system failure");
                }
            }
            // Variable lookup
            ExprKind::Var(id) => self
                .lookup(id)
                .expect(&format!("No binding in scope for var {:?}", id)),
            // Math operators
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
            ExprKind::SubI(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(subexpr_l);
                let arg_r = self.eval_expr(subexpr_r);
                if let (Value::Int(i1), Value::Int(i2)) = (arg_l, arg_r) {
                    Value::Int(i1 - i2)
                } else {
                    panic!("Runtime type error: arguments to addi aren't ints");
                }
            }
            ExprKind::SubF(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(subexpr_l);
                let arg_r = self.eval_expr(subexpr_r);
                if let (Value::Float(f1), Value::Float(f2)) = (arg_l, arg_r) {
                    Value::Float(f1 - f2)
                } else {
                    panic!("Runtime type error: arguments to addf aren't floats");
                }
            }
            // Type conversion
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
            // Lists
            ExprKind::List(subexprs) => Value::List(
                subexprs
                    .into_iter()
                    .map(|subexpr| self.eval_expr(subexpr))
                    .collect(),
            ),
            ExprKind::Or(_, _) => unimplemented!(),
        }
    }
}

// Execute a query function (lambda) on an argument
fn exec_query_function(ir_env: &IrData, f: &Lambda, arg: &Document) -> Value {
    // Make an evaluator
    let mut evaluator = Evaluator::new(ir_env);
    let Lambda { param, body } = f;
    // Push the parameter to scope
    evaluator.push_scope(param, Value::Object(arg.clone()));
    // eval
    let result = evaluator.eval_expr(&body);
    // We don't have to worry about popping scope because this
    // evaluator is going away anyway.
    result
}

// Takes a dabatase connection and IR collection object, and returns a
// vector of documents in that collection.
fn coll_docs(db_conn: &Database, coll: &Collection) -> Vec<Document> {
    db_conn
        .collection(&coll.name.1)
        .find(None, None)
        .unwrap()
        .into_iter()
        .map(|d| d.unwrap())
        .collect()
}

// Replace an object in a collection
fn replace_doc(db_conn: &Database, coll: &Collection, id: ObjectId, new: Document) {
    db_conn
        .collection(&coll.name.1)
        .replace_one(doc! {"_id": id}, new, None)
        .expect("Couldn't replace document");
}

// Add a new object to a collection
fn insert_doc(db_conn: &Database, coll: &Collection, new: Document) {
    db_conn
        .collection(&coll.name.1)
        .insert_one(new, None)
        .expect("Couldn't insert document");
}

// Remove an object from a collection, by id.
fn delete_doc(db_conn: &Database, coll: &Collection, id: ObjectId) {
    db_conn
        .collection(&coll.name.1)
        .delete_one(doc! {"_id": id}, None)
        .expect("Couldn't delete document");
}
