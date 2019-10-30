extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro_crate::crate_name;
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse_macro_input, Attribute, AttributeArgs, Data, DataStruct, DeriveInput, Fields, Lit, Meta,
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
            pub fn #method_ident(&self, id: &Principle) -> Option<&#field_type> {
                if #policy_module::#reader_ident(self).accessible_by(id) {
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
            let field_vis = &field.vis;
            let field_attrs = &field.attrs;
            quote! {
                #(#field_attrs)*
                #field_vis #field_ident: Option<#field_type>
            }
        });
        let field_builders = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            let method_ident = format_ident!("get_{}", field_ident);
            quote! {
                #field_ident: self.#method_ident(id).map(|s| s.clone())
            }
        });
        quote! {
            #[derive(Debug)]
            #input_vis struct #partial_ident {
                #(#optioned_fields),*,
                id: Option<#enforcement_crate_name::RecordId>
            }
            impl #ident {
                pub fn fully_resolve(&self, id: &Principle) -> #partial_ident {
                    #partial_ident {
                        #(#field_builders),*,
                        id: self.id.clone()
                    }
                }
            }
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
                        id: Some(doc.get_object_id("_id").unwrap().clone())
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
        let ident_string = ident.to_string();
        quote!{
            impl DBCollection for #ident {
                fn find_by_id(connection: AuthConn, id: RecordId) -> Option<Self> {
                    match connection
                        .conn()
                        .mongo_conn
                        .collection(#ident_string)
                        .find_one(Some(doc! {"_id":id}), None)
                    {
                        Result::Ok(Some(doc)) => Some(#ident::from_document(doc)),
                        _ => None,
                    }
                }
                fn insert_many(connection: AuthConn, items: Vec<Self>) -> Option<Vec<RecordId>> {
                    match connection.conn().mongo_conn.collection(#ident_string)
                        .insert_many(items.iter().map(#ident::to_document).collect(), None)
                    {
                        Result::Ok(mongodb::coll::results::InsertManyResult {
                            inserted_ids: Some(ids), ..
                        }) => Some(
                            // Unwrap is safe because these are guaranteed to be ids
                            ids.values().map(|b| b.as_object_id().unwrap().clone())
                                .collect()),
                       _ => None,
                    }
                }
            }
        }
    };

    // Field enum
    let enum_ident = format_ident!("{}Fields", ident);
    let fields_enum = {
        let field_enum_idents = fields.iter().map(|field| {
            format_ident!("{}", capitalize_string(field.ident.as_ref()
                                                  .unwrap().to_string()))
        });
        quote! {
            pub enum #enum_ident {
                #(#field_enum_idents),*
            }
        }
    };

    // implementations for checked "save" and "save_all" methods
    let save_impl = {
        let enum_ident = format_ident!("{}Fields", ident);
        let ident_string = ident.to_string();
        let field_check_arms = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            let capitalized_ident = format_ident!("{}",
                                                  capitalize_string(field_ident.to_string()));
            let write_ident = format_ident!("write_{}", field_ident);
            let read_ident = format_ident!("read_{}", field_ident);
            quote!{
                #enum_ident::#capitalized_ident => {
                    if ! #policy_module::#write_ident(item)
                        .accessible_by(&connection.principle()) ||
                        ! #policy_module::#read_ident(item)
                        .accessible_by(&connection.principle())
                    {
                        return false;
                    }
                }
            }
        });
        let field_set_arms = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            let capitalized_ident = format_ident!("{}",
                                                  capitalize_string(field_ident.to_string()));
            let get_ident = format_ident!("get_{}", field_ident);
            let field_str = field_ident.to_string();
            quote!{
                #enum_ident::#capitalized_ident => {
                    set_doc.insert(#field_str,
                                   item.#get_ident(&connection.principle())
                                   .expect("Can't save fields without read permissions!"))
                }
            }
        });
        quote!{
            impl #ident {
                pub fn save_all(connection: AuthConn, items: Vec<&#ident>, fields: Vec<#enum_ident>) -> bool {
                    for item in items.iter() {
                        for field in fields.iter() {
                            match field {
                                #(#field_check_arms),*
                            };
                        }
                    }
                    for item in items.into_iter() {
                        let get_doc = doc! {
                            "_id": item.id.clone().expect("Tried to modify an object not from the database!")
                        };
                        let mut set_doc = bson::Document::new();
                        for field in fields.iter() {
                            match field {
                                #(#field_set_arms),*
                            };
                        }
                        connection
                            .conn()
                            .mongo_conn
                            .collection(#ident_string)
                            .update_one(get_doc, doc! {"$set": set_doc}, None)
                            .unwrap();
                    }
                    true
                }
                pub fn save(&self, connection: AuthConn, fields: Vec<UserFields>) -> bool{
                    User::save_all(connection, vec![&self], fields)
                }
            }
        }
    };

    // Build the output, possibly using quasi-quotation
    let expanded = quote! {
        use mongodb::db::ThreadedDatabase;
        #input_with_id
        #getter_impl
        #setter_impl
        #constructor
        #partial_type
        #mongo_doc_impl
        #dbcoll_impl
        #fields_enum
        #save_impl
    };

    // Hand the output tokens back to the compiler
    TokenStream::from(expanded)
}

fn capitalize_string(s : String) -> String {
    let mut result_string = s;
    if let Some(r) = result_string.get_mut(0..1) {
        r.make_ascii_uppercase();
    } else {
        unreachable!("Cannot capitalize something without any letters!")
    }
    result_string
}
