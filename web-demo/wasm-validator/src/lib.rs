extern crate wasm_bindgen;

use policy_lang::ast::{GlobalPolicy, Migration};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct OpaqueGlobalPolicy(GlobalPolicy);

#[wasm_bindgen]
pub fn parse_policy(pol: &str) -> Result<OpaqueGlobalPolicy, JsValue> {
    policy_lang::parse_policy(pol)
        .map(OpaqueGlobalPolicy)
        .map_err(|e| JsValue::from_serde(&e).unwrap())
}

#[wasm_bindgen]
pub struct OpaqueMigration(Migration);

#[wasm_bindgen]
pub fn parse_migration(migration: &str) -> Result<OpaqueMigration, JsValue> {
    policy_lang::parse_migration(migration)
        .map(OpaqueMigration)
        .map_err(|e| JsValue::from_serde(&e).unwrap())
}
