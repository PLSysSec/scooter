use policy_lang::ir::{schema::Schema, expr::Func};
use policy_lang::ir::policy::{CollectionPolicy, FieldPolicy};


pub(crate) fn check_collection_refine(schema: &Schema,
                                      old_collection_policy: CollectionPolicy,
                                      new_collection_poilcy: CollectionPolicy) -> bool {
    unimplemented!("Define in terms of is_as_strict")
}

pub(crate) fn check_field_refine(schema: &Schema,
                                 old_field_policy: FieldPolicy,
                                 new_field_policy: FieldPolicy) -> bool {
    unimplemented!("Define in terms of is_as_strict")
}

pub(crate) fn is_as_strict(schema: &Schema, before: &Func, after: &Func) -> bool {
    unimplemented!("Be back soon");
}
