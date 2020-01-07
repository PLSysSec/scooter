extern crate proc_macro;

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{
    parse_macro_input, AttributeArgs, Data, DataStruct, DeriveInput, Fields, Lit, Meta,
    NestedMeta,
};

#[proc_macro_attribute]
pub fn collection(args: TokenStream, item: TokenStream) -> TokenStream {
    // Parse the attribute arguments, setting the "policy_module" argument
    let args_input = parse_macro_input!(args as AttributeArgs);
    assert_eq!(args_input.len(), 1, "Not the right number of arguments!");
    let mv = match args_input.into_iter().next().unwrap() {
        NestedMeta::Meta(Meta::NameValue(m)) => m,
        _ => panic!("Expects argument of the form policy_module=<module>"),
    };
    assert_eq!(
        mv.path.get_ident().expect("Bad identifier as argument"),
        "policy_module",
        "Only valid argument is \"policy_module\""
    );
    let policy_module = match mv.lit {
        Lit::Str(s) => format_ident!("{}", s.value()),
        _ => panic!("Expects a string argument for policy_module"),
    };
    let enforcement_crate_name = format_ident!("enforcement");

    // Parse the actual struct, and retrieve it's fields
    let input = parse_macro_input!(item as DeriveInput);
    let ident = input.ident;
    let ident_string = ident.to_string();
    let fields = match input.data {
        Data::Struct(DataStruct {
            fields: Fields::Named(fs),
            ..
        }) => fs.named,
        _ => panic!("Collections must be structs with named fields"),
    };
    let input_vis = input.vis;
    let input_with_id = {
        let fields_iter = fields.iter();
        quote! {
            #input_vis struct #ident {
                #(#fields_iter),*,
                pub id: Option<#enforcement_crate_name::RecordId>
            }
        }
    };
    // Generate getters for each of the getters
    let field_getters = fields.iter().map(|field| {
        let field_ident = field.ident.as_ref().unwrap();
        let field_type = &field.ty;
        let method_ident = format_ident!("get_{}", field_ident);
        let reader_ident = format_ident!("read_{}", field_ident);
        quote! {
            #[allow(dead_code)]
            pub fn #method_ident(&self, conn: &AuthConn) -> Option<&#field_type> {
                if #policy_module::#reader_ident(self, conn).accessible_by(&conn.principle()) {
                    Some(&self.#field_ident)
                } else {
                    None
                }
            }
        }
    });
    let getter_impl = quote! {
        impl #ident {
            #(#field_getters)*
        }
    };
    let field_setters = fields.iter().map(|field| {
        let field_ident = field.ident.as_ref().unwrap();
        let field_type = &field.ty;
        let method_ident = format_ident!("set_{}", field_ident);
        quote! {
            #[allow(dead_code)]
            pub fn #method_ident(&mut self, val : #field_type) {
                self.#field_ident = val;
            }
        }
    });
    let setter_impl = quote! {
        impl #ident {
            #(#field_setters)*
        }
    };
    let constructor = {
        let prop_ident = format_ident!("{}Props", ident);
        let pub_fields = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            let field_type = &field.ty;
            let field_attrs = &field.attrs;
            quote! {
                #(#field_attrs)*
                pub #field_ident: #field_type
            }
        });
        let field_inits = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            quote! {
                #field_ident: props.#field_ident
            }
        });
        quote! {
            pub struct #prop_ident {
                #(#pub_fields),*
            }
            impl #ident {
                pub fn new(props : #prop_ident) -> #ident{
                    #ident{
                        #(#field_inits),*,
                        id:None
                    }
                }
            }
        }
    };
    // Partial type
    let partial_ident = format_ident!("Partial{}", ident);
    let partial_type = {
        let optioned_fields = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            let field_type = &field.ty;
            let field_attrs = &field.attrs;
            quote! {
                #(#field_attrs)*
                pub #field_ident: Option<#field_type>
            }
        });
        let field_builders = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            let method_ident = format_ident!("get_{}", field_ident);
            quote! {
                #field_ident: self.#method_ident(conn).map(|s| s.clone())
            }
        });
        let builder_fields = optioned_fields.clone();
        let builder = {
            let builder_ident = format_ident!("Build{}", ident);
            let field_inits = fields.iter().map(|field| {
                let field_ident = field.ident.as_ref().unwrap();
                quote! { #field_ident: None }
            });
            let field_adders = fields.iter().map(|field| {
                let field_ident = field.ident.as_ref().unwrap();
                let field_type = &field.ty;
                quote! {
                    pub fn #field_ident(&mut self, val: #field_type) -> & mut #builder_ident{
                        self.#field_ident = Some(val);
                        self
                    }
                }
            });
            let field_setters = fields.iter().map(|field| {
                let field_ident = field.ident.as_ref().unwrap();
                quote! {
                    #field_ident: self.#field_ident.clone()
                }
            });
            quote! {
                #input_vis struct #builder_ident {
                    #(#builder_fields),*,
                    id: #enforcement_crate_name::RecordId
                }
                impl #builder_ident {
                    pub fn new(object_id: RecordId) -> #builder_ident{
                        #builder_ident { #(#field_inits),*, id: object_id }
                    }
                    #(#field_adders)*
                    pub fn finalize(&self) -> #partial_ident {
                        #partial_ident {#(#field_setters),*,id:self.id.clone()}
                    }
                }
            }
        };
        quote! {
            #[derive(Debug)]
            #input_vis struct #partial_ident {
                #(#optioned_fields),*,
                id: #enforcement_crate_name::RecordId
            }
            impl #ident {
                pub fn fully_resolve(&self, conn: &AuthConn) -> #partial_ident {
                    #partial_ident {
                        #(#field_builders),*,
                        id: self.id.clone()
                            .expect("Can't resolve an object without an id!")
                    }
                }
            }
            #builder
        }
    };


    // Mongo document conversion
    let mongo_doc_impl = {
        let doc_set_fields = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            let field_str = field_ident.to_string();
            quote! {
                #field_str: self.#field_ident.to_bson()
            }
        });
        let doc_get_fields = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            let field_str = field_ident.to_string();
            let field_type = &field.ty;
            quote! {
                #field_ident: <#field_type>::from_bson(doc.remove(#field_str).unwrap())
            }
        });
        quote! {
            impl MongoDocument for #ident {
                fn from_document(mut doc: mongodb::Document) -> Self {
                    #ident {
                        #(#doc_get_fields),*,
                        id: Some(doc.get_object_id("_id").unwrap().clone().into())
                    }
                }
                fn to_document(&self) -> mongodb::Document {
                    let mut doc = doc! {
                        #(#doc_set_fields),*
                    };
                    if let Some(id) = &self.id {
                        doc.insert("_id", id.clone());
                    };
                    doc
                }
            }
        }
    };
    let dbcoll_impl = {
        let save_all_impl = {
            let field_check_write_partial_arms = fields.iter().map(|field| {
                let field_ident = field.ident.as_ref().unwrap();
                let write_ident = format_ident!("write_{}", field_ident);
                quote!{
                    if item.#field_ident.is_some() &&
                        ! #policy_module::#write_ident(&full_item, &connection)
                        .accessible_by(&connection.principle()) {
                            return false
                    }
                }
            });
            let field_set_partial_arms = fields.iter().map(|field| {
                let field_ident = field.ident.as_ref().unwrap();
                let field_str = field_ident.to_string();
                quote!{
                    if let Some(v) = &item.#field_ident {
                        set_doc.insert(#field_str, v.clone());
                    }
                }
            });
            quote!{
                fn save_all(connection: &AuthConn, items: Vec<&#partial_ident>) -> bool {
                    use mongodb::db::ThreadedDatabase;
                    for item in items.iter() {
                        let get_doc = doc! {
                            "_id": item.id.clone()
                        };
                        let full_item = #ident::from_document(
                            connection
                                .conn()
                                .mongo_conn
                                .collection(#ident_string)
                                .find_one(Some(doc! {"_id":item.id.clone()}),
                                          None)
                                .unwrap()
                                .expect("Tried to modify an object not from the database!"));
                        #(#field_check_write_partial_arms)*
                    }
                    for item in items.into_iter() {
                        let get_doc = doc! {
                            "_id": item.id.clone()
                        };
                        let mut set_doc = bson::Document::new();
                        #(#field_set_partial_arms)*
                        connection
                            .conn()
                            .mongo_conn
                            .collection(#ident_string)
                            .update_one(get_doc, doc! {"$set": set_doc}, None)
                            .unwrap();
                    }
                    true
                }
            }
        };
        quote!{
            impl DBCollection for #ident {
                type Partial=#partial_ident;
                fn find_by_id(connection: &AuthConn, id: RecordId) -> Option<Self::Partial> {
                    match Self::find_full_by_id(connection.conn(), id) {
                        Some(item) => Some(item.fully_resolve(connection)),
                        None => None,
                    }
                }
                fn find_full_by_id(connection: &DBConn, id: RecordId) -> Option<Self> {
                    use mongodb::db::ThreadedDatabase;
                    match connection.mongo_conn
                        .collection(#ident_string)
                        .find_one(Some(doc! {"_id":id}), None)
                    {
                        Result::Ok(Some(doc)) => Some(#ident::from_document(doc)),
                        _ => None,
                    }
                }
                fn insert_one(connection: &AuthConn, item: Self) -> Option<TypedRecordId<Self>> {
                    Self::insert_many(connection, vec![item]).map(|v| v.into_iter().next().expect("Got an empty vec"))
                }
                fn insert_many(connection: &AuthConn, items: Vec<Self>) -> Option<Vec<TypedRecordId<Self>>> {
                    use mongodb::db::ThreadedDatabase;
                    for item in items.iter() {
                        if ! #policy_module::create(&item, connection)
                            .accessible_by(&connection.principle()) {
                                return None
                            }
                    }
                    match connection.conn().mongo_conn.collection(#ident_string)
                        .insert_many(items.iter().map(#ident::to_document).collect(), None)
                    {
                        Result::Ok(mongodb::coll::results::InsertManyResult {
                            inserted_ids: Some(ids), ..
                        }) => Some(
                            // Unwrap is safe because these are guaranteed to be ids
                            ids.values().map(|b| b.as_object_id().unwrap().clone().into())
                                .collect()),
                       _ => None,
                    }
                }
                fn delete_by_id(connection: &AuthConn, id: RecordId) -> bool {
                    use mongodb::db::ThreadedDatabase;
                    match connection
                        .conn()
                        .mongo_conn
                        .collection(#ident_string)
                        .find_one(Some(doc! {"_id":id.clone()}), None)
                    {
                        Result::Ok(Some(doc)) =>
                            if ! #policy_module::delete(&#ident::from_document(doc),
                                                        connection)
                            .accessible_by(&connection.principle()){
                                return false
                            }
                        _ => return false
                    };
                    match connection.conn().mongo_conn.collection(#ident_string)
                        .delete_one(doc! {"_id":id}, None)
                    {
                        Result::Ok(mongodb::coll::results::DeleteResult {
                            acknowledged: True, ..
                        }) => true,
                        _ => false
                    }
                }
                #save_all_impl
            }
        }
    };

    // implementations for ".save" helper method on partials
    let save_impl = {
        quote!{
            impl #partial_ident {
                pub fn save(&self, connection: &AuthConn) -> bool{
                    #ident::save_all(&connection, vec![self])
                }
            }
        }
    };

    // Build the output, possibly using quasi-quotation
    let expanded = quote! {
        #input_with_id
        #getter_impl
        #setter_impl
        #constructor
        #partial_type
        #mongo_doc_impl
        #dbcoll_impl
        #save_impl
    };

    // Hand the output tokens back to the compiler
    TokenStream::from(expanded)
}
