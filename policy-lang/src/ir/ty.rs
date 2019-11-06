pub struct TypeId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Prim(Prim),
    Id(CollectionId),
    Collection(CollectionId)
}

#[Derive(Debug)]
pub enum Prim {
    Any
}

#[derive(Debug)]
pub struct Collection {
    pub ident: Ident,
    pub fields: HashMap<String, Field>,
}

#[derive(Debug)]
pub struct Field(IrId, Ident);

impl Field {
    pub fn ident(&self) -> Ident {
        self.0
    }

    pub fn def_id(&self) -> IrId {
        self.1
    }
}

