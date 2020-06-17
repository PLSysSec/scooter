// yet to be hooked up!

#[derive(Debug)]
pub struct CompleteMigration(pub Vec<CompleteMigrationCommand>);

#[derive(Debug)]
pub enum CompleteMigrationCommand {
    CollAction {
        table: Id<Collection>,
        action: CompleteMigrationAction,
    },
    Create {
        table_id: Id<Collection>,
    },
    Delete {
        table_id: Id<Collection>,
    },
}

#[derive(Debug)]
pub enum CompleteObjectCommand {
    CreateObject {
        collection: Id<Collection>,
        value: Id<Expr>,
    },
    DeleteObject {
        collection: Id<Collection>,
        id_expr: Id<Expr>,
    },
}
#[derive(Debug)]
pub enum CompleteMigrationAction {
    RemoveField {
        field: Id<Def>,
    },
    AddField {
        field: Id<Def>,
        ty: Type,
        init: Lambda,
    },
    ChangeField {
        field: Id<Def>,
        new_ty: Type,
        new_init: Lambda,
    },
    RenameField {
        old_field_id: Id<Def>,
        new_field_id: Id<Def>,
        old_name: String,
        new_name: String,
    },
    ForEach {
        param: Id<Def>,
        body: CompleteObjectCommand,
    },
    LoosenFieldPolicy {
        new_field_policy: FieldPolicy,
    },
    TightenFieldPolicy {
        new_field_policy: FieldPolicy,
    },
    LoosenCollectionPolicy {
        new_collection_policy: CollectionPolicy,
    },
    TightenCollectionPolicy {
        new_collection_policy: CollectionPolicy,
    },
}