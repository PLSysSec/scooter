extern crate proc_macro;

use proc_macro::TokenStream;
use quote::{quote, ToTokens, format_ident};
use syn::{parse_macro_input, Attribute, AttributeArgs, DeriveInput, Meta, NestedMeta, Lit, Data, DataStruct, Fields};
use proc_macro_crate::crate_name;

#[proc_macro_attribute]
pub fn collection(args: TokenStream, item: TokenStream) -> TokenStream {
    // Parse the attribute arguments, setting the "policy_module" argument
    let args_input = parse_macro_input!(args as AttributeArgs);
    assert_eq!(args_input.len(), 1, "Not the right number of arguments!");
    let mv = match args_input.into_iter().next().unwrap() {
        NestedMeta::Meta(Meta::NameValue(m)) => m,
        _ => panic!("Expects argument of the form policy_module=<module>"),
    };
    assert_eq!(mv.path.get_ident().expect("Bad identifier as argument"), "policy_module",
               "Only valid argument is \"policy_module\"");
    let policy_module = match mv.lit {
        Lit::Str(s) => format_ident!("{}", s.value()),
        _ => panic!("Expects a string argument for policy_module")
    };
    let enforcement_crate_name = format_ident!("enforcement");

    // Parse the actual struct, and retrieve it's fields
    let input = parse_macro_input!(item as DeriveInput);
    let ident = input.ident;
    let fields = match input.data {
        Data::Struct(DataStruct { fields: Fields::Named(fs), .. }) => fs.named,
        _ => panic!("Collections must be structs with named fields")
    };
    let input_vis = input.vis;
    let input_with_id = {
        let fields_iter = fields.iter();
        quote!{
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
        quote!{
            pub fn #method_ident(&self, id: &PrincipleId) -> Option<&#field_type> {
                if #policy_module::#field_ident(self).accessible_by(id) {
                    Some(&self.#field_ident)
                } else {
                    None
                }
            }
        }
    });
    let getter_impl = quote!{
        impl #ident {
            #(#field_getters)*
        }
    };
    let constructor = {
        let field_params = fields.iter().map(|field| {
            let ident = field.ident.as_ref().unwrap();
            let ty = &field.ty;
            quote!{#ident:#ty}
        });
        let field_inits = fields.iter().map(|field| {
            let ident = field.ident.as_ref().unwrap();
            quote!{#ident}
        });
        let constructor_ident = format_ident!("mk_{}",
                                              ident.to_string().to_ascii_lowercase());
        quote!{
            pub fn #constructor_ident(#(#field_params),*) -> #ident {
                #ident{#(#field_inits),*,id:None}
            }
        }
    };
    // Resolved type
    let resolved_type = {
        let optioned_fields = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            let field_type = &field.ty;
            let field_vis = &field.vis;
            let field_attrs = &field.attrs;
            quote!{
                #(#field_attrs)*
                #field_vis #field_ident: Option<#field_type>
            }
        });
        let resolved_ident = format_ident!("Resolved{}", ident);
        let field_builders = fields.iter().map(|field| {
            let field_ident = field.ident.as_ref().unwrap();
            let method_ident = format_ident!("get_{}", field_ident);
            quote!{
                #field_ident: self.#method_ident(id).map(|s| s.clone())
            }
        });
        quote! {
            #[derive(Debug)]
            #input_vis struct #resolved_ident {
                #(#optioned_fields),*,
                id: Option<#enforcement_crate_name::RecordId>
            }
            impl #ident {
                pub fn fully_resolve(&self, id: &PrincipleId) -> #resolved_ident {
                    #resolved_ident {
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

    // Build the output, possibly using quasi-quotation
    let expanded = quote! {
        #input_with_id
        #getter_impl
        #constructor
        #resolved_type
        #mongo_doc_impl
    };

    // Hand the output tokens back to the compiler
    TokenStream::from(expanded)
}
