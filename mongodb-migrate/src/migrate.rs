use policy_lang::{self, ir::expr::ExprType};
use std::iter;

use policy_lang::ir::expr::{FieldComparison, Func, IRExpr, Var};
use policy_lang::ir::migration::{extract_migration_steps, DataCommand, MigrationCommand};
use policy_lang::ir::policy::{extract_schema_policy, SchemaPolicy};
use policy_lang::ir::schema::{Collection, Schema};
use policy_lang::ir::*;

use bson::{doc, oid::ObjectId, Bson, Document};
use chrono;
use chrono::TimeZone;
use mongodb::{Client, Database};

/// Descriptor for the mongodb database a migration would operate on
pub struct DbConf {
    pub host: String,
    pub port: u16,
    pub db_name: String,
}
const MIGRATION_HISTORY_COLL: &str = "migrations-run";
/// Migrate a database, whose schema is outlined in a policy file,
/// using migration commands specified in a migration file.
///
/// # Arguments
///
/// * `db_conf` - Configuration for the database
///
/// * `policy_text` - The policy-lang source specifying the intial
/// configuration of the database
///
/// * `migration_text` - The migration-lang source specifying the
/// migration
pub fn migrate(
    db_conf: DbConf,
    policy_text: &str,
    migration_text: &str,
    migration_name: &str,
) -> Result<(), String> {
    // Parse the policy text into an ast
    let policy_ast = policy_lang::parse_policy(&policy_text).expect("Couldn't parse policy");
    // Parse the migration text into an ast
    let migration_ast =
        policy_lang::parse_migration(&migration_text).expect("Couldn't parse migration");
    // Extract the type information from the policy ast
    let initial_schema_policy = extract_schema_policy(&policy_ast).unwrap();
    let migration_steps =
        extract_migration_steps(&initial_schema_policy.schema, migration_ast).unwrap();
    if migration_already_run(&db_conf, migration_name) {
        Err("This migration has already been run!".to_string())
    } else {
        // Do this first in case it fails for some reason
        mark_migration_run(&db_conf, migration_name);
        // Run the migration
        interpret_migration(db_conf, initial_schema_policy, migration_steps);
        Ok(())
    }
}

pub fn reset_migration_history(db_conf: &DbConf) {
    let db_conn = Client::with_uri_str(&format!("mongodb://{}:{}", db_conf.host, db_conf.port))
        .expect("Failed to initialize client.")
        .database(&db_conf.db_name);
    db_conn.collection(MIGRATION_HISTORY_COLL).drop(None).ok();
}

/// Interpret the commands in a migration file, using a given database
/// and policy environment.
///
/// # Arguments
///
/// `db_conf` - Configuration for the database to run the migration on
///
/// `migration_ast` - The parsed migration (a list of migration commands)
///
/// `policy_env` - The type environment on the original policy (pre-migration)
///
/// `policy_ir` - The original policy itself
fn interpret_migration(
    db_conf: DbConf,
    initial_schema_policy: SchemaPolicy,
    migration_steps: Vec<(Schema, MigrationCommand)>,
) {
    // Create a connection to the database
    let db_conn = Client::with_uri_str(&format!("mongodb://{}:{}", db_conf.host, db_conf.port))
        .expect("Failed to initialize client.")
        .database(&db_conf.db_name);
    // Loop over the migration commands in sequence
    for (schema_before, (_schema_after, cmd)) in iter::once(&initial_schema_policy.schema)
        .chain(migration_steps.iter().map(|(schema, _cmd)| schema))
        .zip(migration_steps.iter())
    {
        match cmd {
            // Remove field command. Removes a field from all records in the collection.
            MigrationCommand::RemoveField { coll, field } => {
                let coll = &schema_before[coll];
                // Loop over the records
                for item in coll_docs(&db_conn, &coll).into_iter() {
                    // Get the item id for replacement
                    let item_id = item.get_object_id("_id").unwrap().clone();
                    let mut result = item;
                    // Remove the field from the mongo doc object
                    result.remove(&field.orig_name);
                    replace_doc(&db_conn, &coll, item_id, result);
                }
            }
            // Add a field to all records in the collection
            MigrationCommand::AddField {
                coll,
                field,
                ty: _,
                init,
                pol: _,
            } => {
                let coll = &schema_before[coll];
                // Loop over the records
                for item in coll_docs(&db_conn, &coll).into_iter() {
                    // Get the item id for replacement
                    let item_id = item.get_object_id("_id").unwrap().clone();
                    let mut result = item;
                    let field_name = field.orig_name.clone();
                    assert!(
                        !result.contains_key(&field_name),
                        "Document already contained a field with the name \"{}\"",
                        field_name
                    );
                    // Insert the field into the object
                    result.insert(
                        field_name,
                        exec_query_function(&schema_before, &init, &result, &db_conn),
                    );
                    replace_doc(&db_conn, coll, item_id, result);
                }
            }
            // Change the value and type of a field, but not its name.
            MigrationCommand::ChangeField {
                coll,
                field,
                new_ty: _,
                new_init,
            } => {
                let coll = &schema_before[coll];
                // Loop over the records
                for item in coll_docs(&db_conn, &coll).into_iter() {
                    // Get the object
                    let item_id = item.get_object_id("_id").unwrap().clone();
                    let mut result = item;
                    let field_name = field.orig_name.clone();
                    assert!(
                        result.contains_key(&field_name),
                        "Document doesn't contain a field with the name \"{}\"",
                        field_name
                    );
                    // Insert the new field value into the object. Note
                    // that here, we don't have to worry about changing
                    // the type, as that is handled entirely at the
                    // IR/typechecking level.
                    result.insert(
                        field_name,
                        exec_query_function(&schema_before, &new_init, &result, &db_conn),
                    );
                    replace_doc(&db_conn, &coll, item_id, result);
                }
            }
            // Change the name of a field, but not its value or type. Note
            // that Coll::RenameField(field, new_name) is semantically
            // equivalent to Coll::Addfield(new_name, old_type, x ->
            // x.field) followed by Coll::DeleteField(field)
            MigrationCommand::RenameField {
                coll,
                field,
                new_name,
            } => {
                let coll = &schema_before[coll];
                // Loop over the records
                for item in coll_docs(&db_conn, &coll).into_iter() {
                    let item_id = item.get_object_id("_id").unwrap().clone();
                    let mut result = item;
                    // Remove the old field, and get its value.
                    let field_value = result.remove(&field.orig_name).expect(&format!(
                        "Document doesn't contain a field with the name \"{}\"",
                        field.orig_name
                    ));
                    // Insert the new field, making sure there didn't
                    // already exist a field with that name.
                    assert!(
                        result
                            .insert(new_name.orig_name.clone(), field_value)
                            .is_none(),
                        "Document already contains a field with the name \"{}\"",
                        new_name.orig_name
                    );
                    // Replace the document
                    replace_doc(&db_conn, &coll, item_id, result);
                }
            }
            // Commands on individual objects, including foreachs
            MigrationCommand::DataCommand(cmd) => {
                let mut evaluator = Evaluator::new(&schema_before);
                interpret_data_command(&db_conn, &schema_before, &mut evaluator, &cmd);
            }
            MigrationCommand::UpdateFieldPolicy { .. }
            | MigrationCommand::WeakenFieldPolicy { .. }
            | MigrationCommand::UpdatePolicy { .. }
            | MigrationCommand::WeakenPolicy { .. } => {}
            // Creates and deletes actually only operate at the type system level
            MigrationCommand::Create { .. } | MigrationCommand::Delete { .. } => {}
            // Principal changing also operates at the type system and policy level
            MigrationCommand::AddStaticPrincipal { .. } | MigrationCommand::AddPrincipal { .. } => {
            }
        }
    }
}

fn interpret_data_command(
    db_conn: &Database,
    schema: &Schema,
    evaluator: &mut Evaluator,
    cmd: &DataCommand,
) {
    match cmd {
        DataCommand::ForEach {
            param,
            coll: coll_name,
            body,
        } => {
            let coll = &schema[coll_name];
            for item in coll_docs(&db_conn, &coll).into_iter() {
                // Push the document parameter to the variable stack
                evaluator.push_scope(&param, Value::Object(item.clone()));
                interpret_data_command(db_conn, schema, evaluator, body.as_ref());
                evaluator.pop_scope(&param);
            }
        }
        // Add a new object to a given collection.
        DataCommand::CreateObject { collection, value } => {
            // Evaluate the object expression, and make
            // sure it's an Object value.
            if let Value::Object(obj) = evaluator.eval_expr(db_conn, Box::new(value.clone())) {
                // Static checking should ensure that it's
                // the right kind of object (has all the
                // fields), so we're not going to check
                // that here.
                insert_doc(&db_conn, &schema[collection], obj)
            } else {
                // If it's not, something must have gone
                // wrong with static checking.
                panic!("Can't insert these kinds of values; typechecking must have failed");
            }
        }
        // Delete an object from a collectino by it's id.
        DataCommand::DeleteObject {
            collection,
            id_expr,
        } => {
            // Make sure the id expression evaluates to an id value
            if let Value::Id(id) = evaluator.eval_expr(db_conn, Box::new(id_expr.clone())) {
                // Delete the document
                delete_doc(&db_conn, &schema[collection], id)
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
}

/// Possible value types in our languages
#[derive(Clone, Debug, PartialEq)]
enum Value {
    /// Primitive integers
    Int(i64),
    /// Primitive floats
    Float(f64),
    /// Primitive strings
    String(String),
    /// Primitive booleans
    Bool(bool),
    /// Datetimes and Datetime intervals
    DateTime(chrono::DateTime<chrono::Utc>),
    /// Object values. They are represented by the MongoDocument type,
    /// but not all valid MongoDocuments contain valid values, so be
    /// careful.
    Object(Document),
    /// An object ID in the database.
    Id(ObjectId),
    /// A list of possibly heterogenous values
    Set(Vec<Value>),
    /// An optional value
    Option(Option<Box<Value>>),
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
            Value::Set(vs) => Bson::Array(vs.into_iter().map(|v| v.into()).collect()),
            Value::Bool(b) => Bson::Boolean(b),
            Value::DateTime(datetime) => Bson::UtcDatetime(datetime),
            Value::Option(Some(val)) => Bson::from(*val),
            Value::Option(None) => Bson::Document(doc! {"OPTION_exist": false}),
        }
    }
}
impl From<Bson> for Value {
    fn from(b: Bson) -> Value {
        match b {
            Bson::I64(i) => Value::Int(i),
            Bson::FloatingPoint(f) => Value::Float(f),
            Bson::String(s) => match s.as_str() {
                "None" => Value::Option(None),
                _ => Value::String(s),
            },
            Bson::ObjectId(i) => Value::Id(i),
            Bson::Boolean(b) => Value::Bool(b),
            Bson::Array(l) => Value::Set(l.into_iter().map(|v| v.into()).collect()),
            Bson::Null => Value::Option(None),
            Bson::Document(d) => Value::Option(Some(Box::new(
                d.get("Some")
                    .expect("Invalid document in database.")
                    .clone()
                    .into(),
            ))),
            _ => panic!("These kinds of bson objects shouldn't exist"),
        }
    }
}

// A naming environment and value context for evaluating expressinos.
struct Evaluator<'a> {
    pub schema: &'a Schema,
    env: Vec<(Ident<Var>, Value)>,
}

impl Evaluator<'_> {
    fn new(schema: &Schema) -> Evaluator {
        Evaluator {
            schema: schema,
            env: vec![],
        }
    }
    // Push a variable into scope with a value
    fn push_scope(&mut self, id: &Ident<Var>, val: Value) {
        self.env.push((id.clone(), val));
    }
    // Pop the last variable from scope. This takes an identifier
    // again, to make sure you're not popping someone elses variable,
    // but you still need to treat it like a stack.
    fn pop_scope(&mut self, id: &Ident<Var>) {
        assert_eq!(self.env.pop().unwrap().0, *id);
    }
    // Lookup a variable definition in the definition map.
    fn lookup(&self, target_id: &Ident<Var>) -> Option<Value> {
        for (var_id, var_val) in self.env.iter() {
            if var_id == target_id {
                return Some((*var_val).clone());
            }
        }
        None
    }
    // Evaluate an expression down to a value
    fn eval_expr(&mut self, db_conn: &Database, expr: Box<IRExpr>) -> Value {
        match *expr {
            // String append
            IRExpr::AppendS(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(db_conn, subexpr_l);
                let arg_r = self.eval_expr(db_conn, subexpr_r);
                if let (Value::String(s1), Value::String(s2)) = (arg_l, arg_r) {
                    Value::String(s1 + &s2)
                } else {
                    panic!("Arguments to append aren't strings at runtime! Type system failure");
                }
            }
            // Set union
            IRExpr::AppendL(_ty, subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(db_conn, subexpr_l);
                let arg_r = self.eval_expr(db_conn, subexpr_r);
                if let (Value::Set(s1), Value::Set(s2)) = (arg_l, arg_r) {
                    let mut result = s1.clone();
                    result.append(&mut s2.clone());
                    Value::Set(result)
                } else {
                    panic!("Arguments to append aren't strings at runtime! Type system failure");
                }
            }
            IRExpr::DiffL(_ty, subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(db_conn, subexpr_l);
                let arg_r = self.eval_expr(db_conn, subexpr_r);
                if let (Value::Set(s1), Value::Set(s2)) = (arg_l, arg_r) {
                    let result = s1
                        .clone()
                        .into_iter()
                        .filter(|v| !s2.contains(v))
                        .collect::<Vec<_>>();
                    Value::Set(result)
                } else {
                    panic!("Arguments to append aren't strings at runtime! Type system failure");
                }
            }
            // Set intersect
            IRExpr::Intersect(_ty, _subexpr_l, _subexpr_r) => {
                panic!("Intersect isn't yet supported in non-policy functions")
            }
            // Math operators
            IRExpr::AddI(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(db_conn, subexpr_l);
                let arg_r = self.eval_expr(db_conn, subexpr_r);
                if let (Value::Int(i1), Value::Int(i2)) = (arg_l, arg_r) {
                    Value::Int(i1 + i2)
                } else {
                    panic!("Runtime type error: arguments to addi aren't ints");
                }
            }
            IRExpr::AddF(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(db_conn, subexpr_l);
                let arg_r = self.eval_expr(db_conn, subexpr_r);
                if let (Value::Float(f1), Value::Float(f2)) = (arg_l, arg_r) {
                    Value::Float(f1 + f2)
                } else {
                    panic!("Runtime type error: arguments to addf aren't floats");
                }
            }
            IRExpr::AddD(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(db_conn, subexpr_l);
                let arg_r = self.eval_expr(db_conn, subexpr_r);
                if let (Value::DateTime(f1), Value::DateTime(f2)) = (arg_l, arg_r) {
                    Value::DateTime(f1 + (f2 - chrono::Utc.ymd(0, 0, 0).and_hms(0, 0, 0)))
                } else {
                    panic!("Runtime type error: arguments to addf aren't floats");
                }
            }
            IRExpr::SubI(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(db_conn, subexpr_l);
                let arg_r = self.eval_expr(db_conn, subexpr_r);
                if let (Value::Int(i1), Value::Int(i2)) = (arg_l, arg_r) {
                    Value::Int(i1 - i2)
                } else {
                    panic!("Runtime type error: arguments to addi aren't ints");
                }
            }
            IRExpr::SubF(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(db_conn, subexpr_l);
                let arg_r = self.eval_expr(db_conn, subexpr_r);
                if let (Value::Float(f1), Value::Float(f2)) = (arg_l, arg_r) {
                    Value::Float(f1 - f2)
                } else {
                    panic!("Runtime type error: arguments to addf aren't floats");
                }
            }
            IRExpr::SubD(subexpr_l, subexpr_r) => {
                let arg_l = self.eval_expr(db_conn, subexpr_l);
                let arg_r = self.eval_expr(db_conn, subexpr_r);
                if let (Value::DateTime(f1), Value::DateTime(f2)) = (arg_l, arg_r) {
                    Value::DateTime(f1 - (f2 - chrono::Utc.ymd(0, 0, 0).and_hms(0, 0, 0)))
                } else {
                    panic!("Runtime type error: arguments to addf aren't floats");
                }
            }
            // Checking if two values are equal
            IRExpr::IsEq(_ty, se1, se2) => {
                Value::Bool(self.eval_expr(db_conn, se1) == self.eval_expr(db_conn, se2))
            }
            // Negate a boolean
            IRExpr::Not(e) => match self.eval_expr(db_conn, e) {
                Value::Bool(b) => Value::Bool(!b),
                _ => panic!("Runtime type error: argument to 'not' isn't a bool"),
            },
            // Comparison operators
            IRExpr::IsLessI(se1, se2) => {
                match (self.eval_expr(db_conn, se1), self.eval_expr(db_conn, se2)) {
                    (Value::Int(i1), Value::Int(i2)) => Value::Bool(i1 < i2),
                    _ => panic!("Runtime type error: arguments to less than (int) are not ints"),
                }
            }
            IRExpr::IsLessF(se1, se2) => {
                match (self.eval_expr(db_conn, se1), self.eval_expr(db_conn, se2)) {
                    (Value::Float(f1), Value::Float(f2)) => Value::Bool(f1 < f2),
                    _ => {
                        panic!("Runtime type error: arguments to less than (float) are not floats")
                    }
                }
            }
            IRExpr::IsLessD(se1, se2) => {
                match (self.eval_expr(db_conn, se1), self.eval_expr(db_conn, se2)) {
                    (Value::DateTime(f1), Value::DateTime(f2)) => Value::Bool(f1 < f2),
                    _ => {
                        panic!("Runtime type error: arguments to less than (float) are not floats")
                    }
                }
            }
            // Type conversion
            IRExpr::IntToFloat(subexpr) => {
                let arg = self.eval_expr(db_conn, subexpr);
                if let Value::Int(i) = arg {
                    Value::Float(i as f64)
                } else {
                    panic!(
                        "Runtime type error: argument to conversion isn't an int {:?}",
                        arg
                    );
                }
            }
            // Paths are field lookups on an object.
            IRExpr::Path(ty, obj_expr, field) => {
                // Look up the object
                let obj = self.eval_expr(db_conn, obj_expr);
                // Get the string name of the field, using the col_id
                // that the typechecker put in.
                let field_name = field.orig_name.clone();
                // If the field name is "id", then translate it to
                // "_id" for the mongo calls.
                let normalized_field_name = if field_name == "id" {
                    "_id"
                } else {
                    &field_name
                };

                // Get the field value.
                let mut val: Value = match obj {
                    Value::Object(d) => d
                        .get(normalized_field_name)
                        .expect("Retrieved value doesn't have the right field")
                        .clone()
                        .into(),
                    _ => panic!("Cannot get fields of non-object values"),
                };

                if val != Value::Option(None) {
                    let mut outer_ty = ty;
                    while let ExprType::Option(inner_ty) = outer_ty {
                        outer_ty = *inner_ty;
                        val = Value::Option(Some(Box::new(val)));
                    }
                }
                val
            }
            // Variable lookup
            IRExpr::Var(_ty, id) => self
                .lookup(&id)
                .expect(&format!("No binding in scope for var {:?}", id)),
            // An object spefifier, like User { username: "Alex", ...u}
            IRExpr::Object(_col_id, fields, template_obj_expr) => {
                let mut result_object = doc! {};
                // If there's a template value expression, evaluate
                // it.
                let template_obj_val = template_obj_expr
                    .as_ref()
                    .map(|expr| self.eval_expr(db_conn, expr.clone()));

                // Go through the fields provided
                for (field, expr) in fields.iter() {
                    if field.orig_name == "id" {
                        panic!("You can't specify an id field on an object!!");
                    }
                    // Insert the field and it's value into
                    // the object.
                    result_object.insert(
                        field.orig_name.clone(),
                        match expr {
                            Some(e) => self.eval_expr(db_conn, e.clone()),
                            None => match &template_obj_val {
                                Some(Value::Object(template_obj)) => {
                                    template_obj.get(&field.orig_name).unwrap().clone().into()
                                }
                                Some(_) => panic!("Type system error: template is not an object"),
                                None => panic!(
                                    "Missing field {} but didn't provide a template object",
                                    field.orig_name
                                ),
                            },
                        },
                    );
                }
                Value::Object(result_object)
            }
            IRExpr::Map(list_expr, func) => {
                let list_val = self.eval_expr(db_conn, list_expr.clone());
                if let Value::Set(subvals) = list_val {
                    Value::Set(
                        subvals
                            .into_iter()
                            .map(|subval| {
                                self.push_scope(&func.param, subval);
                                let result = self.eval_expr(db_conn, func.body.clone());
                                self.pop_scope(&func.param);
                                result
                            })
                            .collect(),
                    )
                } else {
                    panic!("Runtime type error: value mapped over is not a list");
                }
            }
            IRExpr::FlatMap(list_expr, func) => {
                let list_val = self.eval_expr(db_conn, list_expr.clone());
                if let Value::Set(subvals) = list_val {
                    Value::Set(
                        subvals
                            .into_iter()
                            .flat_map(|subval| {
                                self.push_scope(&func.param, subval);
                                let result = self.eval_expr(db_conn, func.body.clone());
                                self.pop_scope(&func.param);
                                match result {
                                    Value::Set(vals) => vals,
                                    _ => panic!(
                                        "Runtime type error: return of flat map is not a set"
                                    ),
                                }
                            })
                            .collect(),
                    )
                } else {
                    panic!("Runtime type error: value mapped over is not a list");
                }
            }
            IRExpr::Find(coll, query_fields) => {
                let mut doc = bson::Document::new();
                for (op, field, _fty, val) in query_fields.iter() {
                    match op {
                        FieldComparison::Equals => {
                            doc.insert(
                                field.orig_name.clone(),
                                self.eval_expr(db_conn, val.clone()),
                            );
                        }
                        FieldComparison::Greater => {
                            doc.insert(
                                field.orig_name.clone(),
                                doc! {
                                    "$gt": self.eval_expr(db_conn, val.clone()),
                                },
                            );
                        }
                        FieldComparison::GreaterOrEquals => {
                            doc.insert(
                                field.orig_name.clone(),
                                doc! {
                                    "$ge": self.eval_expr(db_conn, val.clone()),
                                },
                            );
                        }
                        FieldComparison::Less => {
                            doc.insert(
                                field.orig_name.clone(),
                                doc! {
                                    "$lt": self.eval_expr(db_conn, val.clone()),
                                },
                            );
                        }
                        FieldComparison::LessOrEquals => {
                            doc.insert(
                                field.orig_name.clone(),
                                doc! {
                                    "$le": self.eval_expr(db_conn, val.clone()),
                                },
                            );
                        }
                        // These are handled in the post-retreive filter
                        FieldComparison::Contains => (),
                    }
                }
                match db_conn
                    .collection(&self.schema[&coll].name.orig_name)
                    .find(Some(doc), None)
                {
                    Result::Ok(cursor) => Value::Set(
                        cursor
                            .filter(|res_bson| {
                                query_fields.iter().all(|(op, field, _fty, val)| {
                                    match op {
                                        // These are handled directly in the query
                                        FieldComparison::Contains => res_bson
                                            .as_ref()
                                            .expect("Failed to fetch document")
                                            .get_array(&field.orig_name)
                                            .unwrap()
                                            .iter()
                                            .any(|elem| {
                                                Value::from(elem.clone())
                                                    == self.eval_expr(db_conn, val.clone())
                                            }),
                                        _ => true,
                                    }
                                })
                            })
                            .map(|res_bson| {
                                Value::Object(res_bson.expect("Failed to fetch document"))
                            })
                            .collect(),
                    ),
                    _ => panic!("Failed to fetch documents"),
                }
            }
            IRExpr::LookupById(coll_id, expr) => match self.eval_expr(db_conn, expr) {
                Value::Id(id) => match db_conn
                    .collection(&self.schema[&coll_id].name.orig_name)
                    .find_one(Some(doc! {"_id": id.clone()}), None)
                {
                    Result::Ok(Some(doc)) => Value::Object(doc),
                    _ => panic!("Couldn't find doc matching id {}", id),
                },
                t => panic!("Runtime type error: lookup argument isn't an id: {:?}", t),
            },
            // Sets
            IRExpr::Set(_ty, subexprs) => Value::Set(
                subexprs
                    .into_iter()
                    .map(|subexpr| self.eval_expr(db_conn, subexpr))
                    .collect(),
            ),
            // Conditional expressions
            IRExpr::If(_ty, cond, e1, e2) => {
                if let Value::Bool(c) = self.eval_expr(db_conn, cond) {
                    if c {
                        self.eval_expr(db_conn, e1)
                    } else {
                        self.eval_expr(db_conn, e2)
                    }
                } else {
                    panic!("Runtime type error: condition of if doesn't evaluate to a bool")
                }
            }
            IRExpr::Match(_ty, opt_expr, var, some_expr, none_expr) => {
                let opt_val = self.eval_expr(db_conn, opt_expr);
                if let Value::Option(oval) = opt_val {
                    match oval {
                        Some(v) => {
                            self.push_scope(&var, *v);
                            let result = self.eval_expr(db_conn, some_expr);
                            self.pop_scope(&var);
                            result
                        }
                        None => self.eval_expr(db_conn, none_expr),
                    }
                } else {
                    panic!(
                        "Runtime type error: scrutinee of match isn't an option.\n{:?}",
                        opt_val
                    );
                }
            }
            IRExpr::Some(_ty, inner_expr) => {
                Value::Option(Some(Box::new(self.eval_expr(db_conn, inner_expr))))
            }
            IRExpr::None(_ty) => Value::Option(None),
            IRExpr::DateTimeConst(datetime) => Value::DateTime(datetime.clone()),
            IRExpr::Now => Value::DateTime(chrono::Utc::now()),
            // Constants evaluate to the constant value
            IRExpr::IntConst(i) => Value::Int(i.clone()),
            IRExpr::FloatConst(f) => Value::Float(f.clone()),
            IRExpr::StringConst(s) => Value::String(s.clone()),
            IRExpr::BoolConst(b) => Value::Bool(b.clone()),
            IRExpr::Public => panic!("We can't run value expressions with `public` in the body"),
        }
    }
}

// Execute a query function (lambda) on an argument
fn exec_query_function(ir_env: &Schema, f: &Func, arg: &Document, db_conn: &Database) -> Value {
    // Make an evaluator
    let mut evaluator = Evaluator::new(ir_env);
    let Func { param, body, .. } = f;
    // Push the parameter to scope
    evaluator.push_scope(&param, Value::Object(arg.clone()));
    // eval
    let result = evaluator.eval_expr(db_conn, body.clone());
    // We don't have to worry about popping scope because this
    // evaluator is going away anyway.
    result
}

// Takes a dabatase connection and IR collection object, and returns a
// vector of documents in that collection.
fn coll_docs(db_conn: &Database, coll: &Collection) -> Vec<Document> {
    db_conn
        .collection(&coll.name.orig_name)
        .find(None, None)
        .unwrap()
        .into_iter()
        .map(|d| d.unwrap())
        .collect()
}

// Replace an object in a collection
fn replace_doc(db_conn: &Database, coll: &Collection, id: ObjectId, new: Document) {
    db_conn
        .collection(&coll.name.orig_name)
        .replace_one(doc! {"_id": id}, new, None)
        .expect("Couldn't replace document");
}

// Add a new object to a collection
fn insert_doc(db_conn: &Database, coll: &Collection, new: Document) {
    db_conn
        .collection(&coll.name.orig_name)
        .insert_one(new, None)
        .expect("Couldn't insert document");
}

// Remove an object from a collection, by id.
fn delete_doc(db_conn: &Database, coll: &Collection, id: ObjectId) {
    db_conn
        .collection(&coll.name.orig_name)
        .delete_one(doc! {"_id": id}, None)
        .expect("Couldn't delete document");
}

fn migration_already_run(db_conf: &DbConf, migration_name: &str) -> bool {
    // Create a connection to the database
    let db_conn = Client::with_uri_str(&format!("mongodb://{}:{}", db_conf.host, db_conf.port))
        .expect("Failed to initialize client.")
        .database(&db_conf.db_name);
    // Look for the migration object
    db_conn
        .collection(MIGRATION_HISTORY_COLL)
        .find_one(Some(doc! {"name": migration_name}), None)
        .expect("Couln't access the database")
        .is_some()
}

fn mark_migration_run(db_conf: &DbConf, migration_name: &str) {
    // Create a connection to the database
    let db_conn = Client::with_uri_str(&format!("mongodb://{}:{}", db_conf.host, db_conf.port))
        .expect("Failed to initialize client.")
        .database(&db_conf.db_name);
    db_conn
        .collection(MIGRATION_HISTORY_COLL)
        .insert_one(doc! {"name": migration_name}, None)
        .expect("Couldn't insert document");
}
