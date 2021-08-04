extern crate proc_macro;

use anyhow::{anyhow, bail, Error};
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote;
use std::{iter, num::NonZeroU32};
use syn::{
    punctuated::Punctuated, Arm, Attribute, Data, DataEnum, DataStruct, DeriveInput, Expr,
    ExprMatch, Field, Fields, FieldsNamed, FieldsUnnamed, GenericParam, Generics, Ident, ItemImpl,
    Lifetime, LifetimeDef, Lit, LitInt, Member, Meta, MetaList, NestedMeta, Token, Type,
    TypeReference, WhereClause, WherePredicate,
};

type Result<T> = std::result::Result<T, Error>;

#[proc_macro_derive(Message, attributes(serde, autoproto))]
pub fn derive_message(input: TokenStream) -> TokenStream {
    try_derive_message(input).unwrap().into()
}

#[proc_macro_derive(Proto, attributes(serde, autoproto))]
pub fn derive_proto(input: TokenStream) -> TokenStream {
    try_derive_proto(input).unwrap().into()
}

#[proc_macro_derive(ProtoEncode, attributes(serde, autoproto))]
pub fn derive_protoencode(input: TokenStream) -> TokenStream {
    try_derive_protoencode(input).unwrap().into()
}

enum DeriveMode {
    ImmutableOnly,
    ImmutableAndMutable,
}

impl Default for DeriveMode {
    fn default() -> Self {
        Self::ImmutableAndMutable
    }
}

fn try_derive_protoencode(input: TokenStream) -> Result<TokenStream2> {
    let input: DeriveInput = syn::parse(input)?;
    let DeriveInput {
        attrs,
        vis: _,
        ident,
        generics,
        data,
    } = &input;

    match data {
        Data::Struct(DataStruct {
            fields: Fields::Named(FieldsNamed { named: fields, .. }),
            ..
        })
        | Data::Struct(DataStruct {
            fields:
                Fields::Unnamed(FieldsUnnamed {
                    unnamed: fields, ..
                }),
            ..
        }) => {
            let protostruct_impl = try_derive_protostruct(
                fields.into_iter(),
                ident,
                generics,
                DeriveMode::ImmutableOnly,
            )?;

            let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
            let make_where_clause = make_where_clause_fn(&generics, where_clause);

            let is_default_where_clause =
                make_where_clause(quote!(::autoproto::IsDefault + ::autoproto::ProtoEncode));
            let is_default_impl = impl_is_default_for_protostruct(
                ident,
                &impl_generics,
                &ty_generics,
                Some(&is_default_where_clause),
            );

            let protoencode_where_clause = make_where_clause(quote!(::autoproto::ProtoEncode));
            let protoencode_impl = impl_protoencode_for_protostruct(
                ident,
                &impl_generics,
                &ty_generics,
                Some(&protoencode_where_clause),
            );

            Ok(quote!(
                #protostruct_impl

                #is_default_impl

                #protoencode_impl
            ))
        }
        Data::Enum(data) => try_derive_enum(&attrs, &ident, generics, data),
        Data::Union(..) => {
            bail!("Message can not be derived for an untagged union (try using `enum`)")
        }
        _ => {
            bail!("Unsupported type for `derive(ProtoEncode)`")
        }
    }
}

fn try_derive_message(input: TokenStream) -> Result<TokenStream2> {
    let input: DeriveInput = syn::parse(input)?;
    let DeriveInput {
        attrs,
        vis: _,
        ident,
        generics,
        data,
    } = &input;

    match data {
        Data::Struct(data) => try_derive_struct(&attrs, &ident, generics, data),
        Data::Enum(data) => try_derive_oneof(&attrs, &ident, generics, data),
        Data::Union(..) => {
            bail!("Message can not be derived for an untagged union (try using `enum`)")
        }
    }
}

fn try_derive_proto(input: TokenStream) -> Result<TokenStream2> {
    let input: DeriveInput = syn::parse(input)?;
    let DeriveInput {
        attrs,
        vis: _,
        ident,
        generics,
        data,
    } = &input;

    match data {
        Data::Struct(data) => try_derive_proto_newtype(&attrs, &ident, generics, data),
        Data::Enum(data) => try_derive_enum(&attrs, &ident, generics, data),
        Data::Union(..) => {
            bail!("Message can not be derived for an untagged union (try using `enum`)")
        }
    }
}

fn try_derive_enum(
    attrs: &[Attribute],
    ident: &Ident,
    generics: &Generics,
    data: &DataEnum,
) -> Result<TokenStream2> {
    todo!()
}

fn try_derive_oneof(
    attrs: &[Attribute],
    ident: &Ident,
    generics: &Generics,
    data: &DataEnum,
) -> Result<TokenStream2> {
    let variants = data
        .variants
        .iter()
        .enumerate()
        .map(|(i, variant)| {
            let attributes = FieldAttributes::new(&variant.attrs)?;

            Ok((
                attributes
                    .tag
                    .unwrap_or(NonZeroU32::new(i as u32 + 1).unwrap()),
                variant,
            ))
        })
        .collect::<Result<Vec<_>>>()?;

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let variant_get_field: Vec<Arm> = variants
        .iter()
        .map::<Arm, _>(|(tag, variant)| {
            let ident = &variant.ident;
            let tag: Lit =
                LitInt::new(&tag.get().to_string(), Span::call_site()).into();

            match &variant.fields {
                Fields::Named(FieldsNamed { named: fields, .. }) => {
                    let names = fields
                        .iter()
                        .map(|field| {
                            field
                                .ident
                                .as_ref()
                                .expect("Programmer error: \"named\" field with no name")
                        })
                        .collect::<Punctuated<_, Token!(,)>>();

                    match fields.len() {
                        0 => {
                            syn::parse_quote!(
                                Self::#ident { } => (
                                    ::core::num::NonZeroU32::new(#tag).unwrap(),
                                    ::std::borrow::Cow::Borrowed(&()),
                                )
                            )
                        }
                        1 => {
                            let field_name = names
                                .first()
                                .expect("Programmer error: names array should have one element");

                            syn::parse_quote!(
                                Self::#ident { #field_name } => (
                                    ::core::num::NonZeroU32::new(#tag).unwrap(),
                                    ::std::borrow::Cow::Borrowed(#field_name),
                                )
                            )
                        }
                        _ => {
                            let lifetime = Lifetime {
                                apostrophe: Span::call_site(),
                                ident: Ident::new("__dummy_lifetime", Span::call_site()),
                            };
                            let dummy_generics = Generics {
                                params: generics
                                    .params
                                    .iter()
                                    .cloned()
                                    .chain(iter::once(GenericParam::Lifetime(LifetimeDef {
                                        attrs: vec![],
                                        lifetime: lifetime.clone(),
                                        colon_token: None,
                                        bounds: Default::default(),
                                    })))
                                    .collect(),
                                ..generics.clone()
                            };

                            let dummy_fields: Punctuated<_, Token!(,)> = fields
                                .iter()
                                .cloned()
                                .map(|field| {
                                    let Field {
                                        attrs,
                                        vis,
                                        ident,
                                        colon_token,
                                        ty,
                                    } = field;

                                    let ty = Type::Reference(TypeReference {
                                        and_token: Default::default(),
                                        lifetime: Some(lifetime.clone()),
                                        mutability: None,
                                        elem: Box::new(ty),
                                    });

                                    Field {
                                        attrs,
                                        vis,
                                        ident,
                                        colon_token,
                                        ty,
                                    }
                                })
                                .collect();

                            let phantom_lifetimes: Vec<Lifetime> = generics.params.iter().filter_map(|g| match g {
                                GenericParam::Lifetime(l) => Some(l.lifetime.clone()),
                                _ => None,
                            }).collect();
                            let phantom_types: Punctuated<Ident, Token!(,)> = generics.params.iter().filter_map(|g| match g {
                                GenericParam::Type(t) => Some(t.ident.clone()),
                                _ => None,
                            }).collect();

                            let mut phantom_inner_type: Type = syn::parse_quote!((#phantom_types));
                            for lifetime in phantom_lifetimes {
                                phantom_inner_type = syn::parse_quote!(& #lifetime phantom_inner_type);
                            }

                            let phantom_name = Ident::new("__proto_dummy_marker", Span::call_site());

                            // TODO: Extract this to function so we don't need to duplicate this
                            //       code both here and for unnamed fields.
                            syn::parse_quote!(
                                Self::#ident { #names } => {
                                    #[derive(Debug, ::autoproto::ProtoEncode)]
                                    struct #ident #dummy_generics {
                                        #dummy_fields,
                                        #phantom_name: ::core::marker::PhantomData<#phantom_inner_type>,
                                    }

                                    (
                                        ::core::num::NonZeroU32::new(#tag).unwrap(),
                                        ::std::borrow::Cow::Owned(
                                            ::std::boxed::Box::new(
                                                #ident :: #ty_generics {
                                                    #names,
                                                    #phantom_name: ::core::marker::PhantomData,
                                                }
                                            ) as ::std::boxed::Box<dyn ::autoproto::ProtoEncode>
                                        ),
                                    )
                                }
                            )
                        }
                    }
                }
                Fields::Unnamed(FieldsUnnamed {
                    unnamed: fields, ..
                }) => {
                    let names = (0..fields.len())
                        .map(|i| {
                            Ident::new(&format!("__field_{}", i), Span::call_site())
                        })
                        .collect::<Punctuated<_, Token!(,)>>();

                    match fields.len() {
                        0 => {
                            syn::parse_quote!(
                                Self::#ident ( ) => (
                                    ::core::num::NonZeroU32::new(#tag).unwrap(),
                                    ::std::borrow::Cow::Borrowed(&()),
                                )
                            )
                        }
                        1 => {
                            let field_name = names
                                .first()
                                .expect("Programmer error: names array should have one element");

                            syn::parse_quote!(
                                Self::#ident ( #field_name ) => (
                                    ::core::num::NonZeroU32::new(#tag).unwrap(),
                                    ::std::borrow::Cow::Borrowed(#field_name),
                                )
                            )
                        }
                        _ => {
                            let lifetime = Lifetime {
                                apostrophe: Span::call_site(),
                                ident: Ident::new("__dummy_lifetime", Span::call_site()),
                            };
                            let dummy_generics = Generics {
                                params: iter::once(
                                    LifetimeDef {
                                        attrs: vec![],
                                        lifetime: lifetime.clone(),
                                        colon_token: None,
                                        bounds: Default::default(),
                                    }.into()
                                )
                                    .chain(
                                        generics
                                            .params
                                            .iter()
                                            .cloned()
                                    )
                                    .collect(),
                                ..generics.clone()
                            };

                            let dummy_fields: Punctuated<_, Token!(,)> = fields
                                .iter()
                                .cloned()
                                .map(|field| {
                                    let Field {
                                        attrs,
                                        vis,
                                        ident,
                                        colon_token,
                                        ty,
                                    } = field;

                                    let ty = Type::Reference(TypeReference {
                                        and_token: Default::default(),
                                        lifetime: Some(lifetime.clone()),
                                        mutability: None,
                                        elem: Box::new(ty),
                                    });

                                    Field {
                                        attrs,
                                        vis,
                                        ident,
                                        colon_token,
                                        ty,
                                    }
                                })
                                .collect();

                            let phantom_lifetimes: Vec<Lifetime> = generics.params.iter().filter_map(|g| match g {
                                GenericParam::Lifetime(l) => Some(l.lifetime.clone()),
                                _ => None,
                            }).collect();
                            let phantom_types: Punctuated<Ident, Token!(,)> = generics.params.iter().filter_map(|g| match g {
                                GenericParam::Type(t) => Some(t.ident.clone()),
                                _ => None,
                            }).collect();

                            let mut phantom_inner_type: Type = syn::parse_quote!((#phantom_types));
                            for lifetime in phantom_lifetimes {
                                phantom_inner_type = syn::parse_quote!(& #lifetime phantom_inner_type);
                            }

                            // TODO: Extract this to function so we don't need to duplicate this
                            //       code both here and for named fields.
                            syn::parse_quote!(
                                Self::#ident ( #names ) => {
                                    #[derive(::autoproto::Message)]
                                    struct #ident #dummy_generics(
                                        #dummy_fields,
                                        ::core::marker::PhantomData<#phantom_inner_type>,
                                    );

                                    (
                                        ::core::num::NonZeroU32::new(#tag).unwrap(),
                                        ::std::borrow::Cow::Owned(
                                            ::std::boxed::Box::new(
                                                #ident :: #ty_generics(
                                                    #names,
                                                    ::core::marker::PhantomData,
                                                )
                                            ) as ::std::boxed::Box<dyn ::autoproto::ProtoEncode>
                                        ),
                                    )
                                }
                            )
                        }
                    }
                },
                Fields::Unit => {
                    syn::parse_quote!(
                        Self::#ident => (
                            ::core::num::NonZeroU32::new(#tag).unwrap(),
                            ::std::borrow::Cow::Borrowed(&()),
                        )
                    )
                }
            }
        })
        .collect();

    let make_where_clause = make_where_clause_fn(&generics, where_clause);

    let protooneof_where_clause = make_where_clause(quote!(::autoproto::Proto));

    let get_variant = ExprMatch {
        attrs: vec![],
        match_token: Default::default(),
        expr: syn::parse_quote!(self),
        brace_token: Default::default(),
        arms: variant_get_field,
    };

    Ok(quote!(
        impl #impl_generics ::autoproto::ProtoOneof for #ident #ty_generics #protooneof_where_clause {
            fn variant(&self) -> (::core::num::NonZeroU32, ::std::borrow::Cow<'_, dyn ::autoproto::ProtoEncode>) {
                #get_variant
            }

            fn exec_merge<F, T>(&mut self, tag: ::core::num::NonZeroU32, func: F) -> Option<T>
            where
                F: FnMut(&mut dyn ::autoproto::Proto) -> T
            {
                todo!()
            }
        }
    ))
}

fn make_where_clause_fn(
    generics: &Generics,
    where_clause: Option<&WhereClause>,
) -> impl Fn(TokenStream2) -> WhereClause {
    let type_params = generics
        .params
        .iter()
        .filter_map(|p| match p {
            GenericParam::Type(t) => Some(t),
            _ => None,
        })
        .map(|t| t.ident.clone())
        .collect::<Vec<_>>();
    let where_clause = where_clause
        .clone()
        .map(WhereClause::clone)
        .unwrap_or(WhereClause {
            where_token: Default::default(),
            predicates: Punctuated::new(),
        });

    move |bound| {
        let mut where_clause = where_clause.clone();

        where_clause.predicates.extend(
            type_params
                .iter()
                .map::<WherePredicate, _>(|bounded_type| syn::parse_quote!(#bounded_type: #bound)),
        );

        where_clause
    }
}

fn try_derive_proto_newtype(
    attrs: &[Attribute],
    ident: &Ident,
    generics: &Generics,
    data: &DataStruct,
) -> Result<TokenStream2> {
    let attrs = MessageAttributes::new(attrs)?;

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    if !attrs.transparent {
        bail!("Cannot derive `Proto` for a non-newtype (try deriving `Message`, which will automatically implement `Proto` for this type too");
    }

    todo!()
}

fn try_derive_protostruct<'a>(
    fields: impl ExactSizeIterator<Item = &'a Field>,
    ident: &Ident,
    generics: &Generics,
    mode: DeriveMode,
) -> Result<TokenStream2> {
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let num_fields = fields.len();

    let make_where_clause = make_where_clause_fn(&generics, where_clause);

    let protostruct_where_clause = make_where_clause(quote!(::autoproto::ProtoEncode));
    let protostructmut_where_clause = make_where_clause(quote!(::autoproto::Proto));

    let fields: Result<Vec<(NonZeroU32, Member)>> = fields
        .enumerate()
        .map(|(i, field)| {
            let attributes = FieldAttributes::new(&field.attrs)?;

            Ok((
                attributes
                    .tag
                    .unwrap_or(NonZeroU32::new(i as u32 + 1).unwrap()),
                field
                    .ident
                    .clone()
                    .map(Member::Named)
                    .unwrap_or(Member::Unnamed(i.into())),
            ))
        })
        .collect();
    let fields = fields?;

    let fields_array: Punctuated<_, Token!(,)> = fields
                    .iter()
                    .map(|(tag, member)| {
                        let tag: Lit =
                            LitInt::new(&tag.get().to_string(), Span::call_site()).into();

                        quote!(
                            (
                                ::core::num::NonZeroU32::new(#tag).unwrap(),
                                ::std::borrow::Cow::Borrowed(&self.#member as &dyn ::autoproto::ProtoEncode),
                            )
                        )
                    })
                    .collect();

    let get_field_mut: Punctuated<Expr, Token!(else)> = fields
        .into_iter()
        .map::<Expr, _>(|(tag, member)| {
            let tag = tag.get();

            syn::parse_quote!(
                if tag.get() == #tag {
                    Some(&mut self.#member)
                }
            )
        })
        .chain(iter::once(syn::parse_quote!({ None })))
        .collect();

    let immut: ItemImpl = syn::parse_quote! {
        impl #impl_generics ::autoproto::ProtoStruct for #ident #ty_generics #protostruct_where_clause {
            type Fields<'__field_lifetime>
            where
                Self: '__field_lifetime
            = [(::core::num::NonZeroU32, ::std::borrow::Cow<'__field_lifetime, dyn ::autoproto::ProtoEncode>); #num_fields];

            fn fields(&self) -> Self::Fields<'_> {
                [#fields_array]
            }
        }
    };
    let mutable: Option<ItemImpl> = match mode {
        DeriveMode::ImmutableOnly => None,
        DeriveMode::ImmutableAndMutable => Some(syn::parse_quote! {
            impl #impl_generics ::autoproto::ProtoStructMut for #ident #ty_generics #protostructmut_where_clause {
                fn field_mut(&mut self, tag: ::core::num::NonZeroU32) -> Option<&mut dyn ::autoproto::Proto> {
                    #get_field_mut
                }
            }
        }),
    };

    Ok(quote! {
        #immut

        #mutable
    })
}

fn try_derive_struct(
    attrs: &[Attribute],
    ident: &Ident,
    generics: &Generics,
    data: &DataStruct,
) -> Result<TokenStream2> {
    let attrs = MessageAttributes::new(attrs)?;

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let make_where_clause = make_where_clause_fn(&generics, where_clause);

    if attrs.transparent {
        let inner_field = match data {
            DataStruct {
                fields: Fields::Named(FieldsNamed { named: fields, .. }),
                ..
            }
            | DataStruct {
                fields:
                    Fields::Unnamed(FieldsUnnamed {
                        unnamed: fields, ..
                    }),
                ..
            } => {
                if fields.len() > 1 {
                    bail!("Cannot have a \"transparent\" message with more than one field");
                }

                fields.first().ok_or(anyhow!("Programmer error"))?
            }
            DataStruct {
                fields: Fields::Unit,
                ..
            } => {
                bail!("Cannot have a \"transparent\" message without fields");
            }
        };

        let field: Member = inner_field
            .ident
            .clone()
            .map(Member::Named)
            .unwrap_or(Member::Unnamed(0.into()));

        let is_default_where_clause = make_where_clause(quote!(::autoproto::IsDefault));
        let proto_where_clause = make_where_clause(quote!(::autoproto::Proto));
        let protoencode_where_clause = make_where_clause(quote!(::autoproto::ProtoEncode));
        let message_where_clause = make_where_clause(quote!(::autoproto::prost::Message));

        return Ok(quote! {
            impl #impl_generics ::autoproto::IsDefault for #ident #ty_generics #is_default_where_clause {
                fn is_default(&self) -> bool {
                    ::autoproto::IsDefault::is_default(&self.#field)
                }
            }

            impl #impl_generics ::autoproto::ProtoEncode for #ident #ty_generics #protoencode_where_clause {
                fn encode_as_field(&self, tag: ::core::num::NonZeroU32, buf: &mut dyn prost::bytes::BufMut) {
                    ::autoproto::ProtoEncode::encode_as_field(&self.#field, tag, buf)
                }

                fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                    ::autoproto::ProtoEncode::encoded_len_as_field(&self.#field, tag)
                }
            }

            impl #impl_generics ::autoproto::Proto for #ident #ty_generics #proto_where_clause {
                fn merge_self(
                    &mut self,
                    wire_type: ::autoproto::prost::encoding::WireType,
                    buf: &mut dyn prost::bytes::Buf,
                    ctx: ::autoproto::prost::encoding::DecodeContext,
                ) -> Result<(), ::autoproto::prost::DecodeError> {
                    ::autoproto::Proto::merge_self(&mut self.#field, wire_type, buf, ctx)
                }
            }

            impl #impl_generics ::autoproto::prost::Message for #ident #ty_generics #message_where_clause {
                fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
                where
                    __Buffer: prost::bytes::BufMut,
                {
                    ::autoproto::prost::Message::encode_raw(&self.#field, buf)
                }

                fn merge_field<__Buffer: prost::bytes::Buf>(
                    &mut self,
                    tag: u32,
                    wire_type: ::autoproto::prost::encoding::WireType,
                    buf: &mut __Buffer,
                    ctx: ::autoproto::prost::encoding::DecodeContext,
                ) -> Result<(), ::autoproto::prost::DecodeError> {
                    ::autoproto::prost::Message::merge_field(&mut self.#field, tag, wire_type, buf, ctx)
                }

                fn encoded_len(&self) -> usize {
                    ::autoproto::prost::Message::encoded_len(&self.#field)
                }

                fn clear(&mut self) {
                    ::autoproto::prost::Message::clear(&mut self.#field)
                }
            }
        }
        .into());
    }

    match data {
        DataStruct {
            fields: Fields::Named(FieldsNamed { named: fields, .. }),
            ..
        }
        | DataStruct {
            fields:
                Fields::Unnamed(FieldsUnnamed {
                    unnamed: fields, ..
                }),
            ..
        } => {
            if fields.is_empty() {
                Ok(unit_proto_impl(
                    ident,
                    impl_generics,
                    ty_generics,
                    where_clause,
                ))
            } else {
                let protostruct_impl = try_derive_protostruct(
                    fields.into_iter(),
                    ident,
                    generics,
                    Default::default(),
                )?;

                let is_default_where_clause = make_where_clause(quote!(::autoproto::ProtoEncode));
                let is_default_impl = impl_is_default_for_protostruct(
                    ident,
                    &impl_generics,
                    &ty_generics,
                    Some(&is_default_where_clause),
                );

                let message_where_clause = make_where_clause(quote!(
                    ::core::default::Default
                        + ::autoproto::Proto
                        + ::core::fmt::Debug
                        + ::core::marker::Send
                        + ::core::marker::Sync
                ));
                let message_impl = impl_message_for_protostruct(
                    ident,
                    &impl_generics,
                    &ty_generics,
                    Some(&message_where_clause),
                );

                let proto_impl =
                    impl_proto_for_message(ident, &impl_generics, &ty_generics, &make_where_clause);

                Ok(quote!(
                    #protostruct_impl

                    #is_default_impl

                    #message_impl

                    #proto_impl
                ))
            }
        }
        DataStruct {
            fields: Fields::Unit,
            ..
        } => Ok(unit_proto_impl(
            ident,
            impl_generics,
            ty_generics,
            where_clause,
        )),
    }
}

fn impl_proto_for_message<F>(
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    make_where_clause: F,
) -> TokenStream2
where
    F: Fn(TokenStream2) -> WhereClause,
{
    let protoencode_where_clause = make_where_clause(quote!(
        ::core::default::Default
            + ::autoproto::IsDefault
            + ::autoproto::Proto
            + ::core::fmt::Debug
            + ::core::marker::Send
            + ::core::marker::Sync
    ));
    let proto_where_clause = make_where_clause(quote!(
        ::core::default::Default
            + ::autoproto::IsDefault
            + ::autoproto::Proto
            + ::core::fmt::Debug
            + ::core::marker::Send
            + ::core::marker::Sync
    ));

    quote!(
        impl #impl_generics ::autoproto::ProtoEncode for #ident #ty_generics #protoencode_where_clause
        {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, mut buf: &mut dyn ::autoproto::prost::bytes::BufMut) {
                ::autoproto::prost::encoding::message::encode(tag.get(), self, &mut buf);
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                ::autoproto::prost::encoding::message::encoded_len(tag.get(), self)
            }
        }

        impl #impl_generics ::autoproto::Proto for #ident #ty_generics #proto_where_clause
        {
            fn merge_self(
                &mut self,
                wire_type: ::autoproto::prost::encoding::WireType,
                mut buf: &mut dyn ::autoproto::prost::bytes::Buf,
                ctx: ::autoproto::prost::encoding::DecodeContext,
            ) -> Result<(), ::autoproto::prost::DecodeError> {
                ::autoproto::prost::encoding::message::merge(wire_type, self, &mut buf, ctx)
            }
        }
    )
}

fn impl_message_for_protooneof(
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> ItemImpl {
    syn::parse_quote!(
        impl #impl_generics ::autoproto::prost::Message for #ident #ty_generics #where_clause
        {
            fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
            where
                __Buffer: ::autoproto::prost::bytes::BufMut,
            {
                ::autoproto::generic::protooneof::message_encode_raw(self, buf)
            }

            fn merge_field<__Buffer: ::autoproto::prost::bytes::Buf>(
                &mut self,
                tag: u32,
                wire_type: ::autoproto::prost::encoding::WireType,
                buf: &mut __Buffer,
                ctx: ::autoproto::prost::encoding::DecodeContext,
            ) -> Result<(), ::autoproto::prost::DecodeError> {
                ::autoproto::generic::protooneof::message_merge_field(self, tag, wire_type, buf, ctx)
            }

            fn encoded_len(&self) -> usize {
                ::autoproto::generic::protooneof::message_encoded_len(self)
            }

            fn clear(&mut self) {
                ::autoproto::generic::default::message_clear(self)
            }
        }
    )
}

fn impl_is_default_for_protostruct(
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> ItemImpl {
    syn::parse_quote!(
        impl #impl_generics ::autoproto::IsDefault for #ident #ty_generics #where_clause {
            fn is_default(&self) -> bool {
                ::autoproto::ProtoStruct::fields(self)
                    .into_iter()
                    .all(|(_, field)| field.is_default())
            }
        }
    )
}

fn impl_is_default_for_protooneof(
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> ItemImpl {
    syn::parse_quote!(
        impl #impl_generics ::autoproto::IsDefault for #ident #ty_generics #where_clause {
            fn is_default(&self) -> bool {
                ::autoproto::generic::default::message_clear(self)
            }
        }
    )
}

fn impl_message_for_protostruct(
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> ItemImpl {
    syn::parse_quote!(
        impl #impl_generics ::autoproto::prost::Message for #ident #ty_generics #where_clause
        {
            fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
            where
                __Buffer: ::autoproto::prost::bytes::BufMut,
            {
                ::autoproto::generic::protostruct::message_encode_raw(self, buf)
            }

            fn merge_field<__Buffer: ::autoproto::prost::bytes::Buf>(
                &mut self,
                tag: u32,
                wire_type: ::autoproto::prost::encoding::WireType,
                buf: &mut __Buffer,
                ctx: ::autoproto::prost::encoding::DecodeContext,
            ) -> Result<(), ::autoproto::prost::DecodeError> {
                ::autoproto::generic::protostruct::message_merge_field(self, tag, wire_type, buf, ctx)
            }

            fn encoded_len(&self) -> usize {
                ::autoproto::generic::protostruct::message_encoded_len(self)
            }

            fn clear(&mut self) {
                ::autoproto::generic::default::message_clear(self)
            }
        }
    )
}

fn impl_protoencode_for_protostruct(
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> ItemImpl {
    syn::parse_quote!(
        impl #impl_generics ::autoproto::ProtoEncode for #ident #ty_generics #where_clause
        {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, mut buf: &mut dyn ::autoproto::prost::bytes::BufMut) {
                let len = ::autoproto::generic::protostruct::message_encoded_len(self);
                let buf = &mut buf;

                ::autoproto::prost::encoding::encode_key(tag.get(), ::autoproto::prost::encoding::WireType::LengthDelimited, buf);
                ::autoproto::prost::encoding::encode_varint(len as u64, buf);
                ::autoproto::generic::protostruct::message_encode_raw(self, buf)
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                let len = ::autoproto::generic::protostruct::message_encoded_len(self);
                ::autoproto::prost::encoding::key_len(tag.get()) +
                    ::autoproto::prost::encoding:: encoded_len_varint(len as u64) +
                    len
            }
        }
    )
}

fn unit_proto_impl(
    ident: &Ident,
    impl_generics: syn::ImplGenerics,
    ty_generics: syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> TokenStream2 {
    quote!(
        impl #impl_generics ::autoproto::IsDefault for #ident #ty_generics #where_clause {
            fn is_default(&self) -> bool {
                true
            }
        }

        impl #impl_generics ::autoproto::ProtoEncode for #ident #ty_generics #where_clause {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, buf: &mut dyn prost::bytes::BufMut) {
                <() as ::autoproto::ProtoEncode>::encode_as_field(&(), tag, buf)
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                <() as ::autoproto::ProtoEncode>::encoded_len_as_field(&(), tag)
            }
        }

        impl #impl_generics ::autoproto::Proto for #ident #ty_generics #where_clause {
            fn merge_self(
                &mut self,
                wire_type: ::autoproto::prost::encoding::WireType,
                buf: &mut dyn ::autoproto::prost::bytes::Buf,
                ctx: ::autoproto::prost::encoding::DecodeContext,
            ) -> Result<(), ::autoproto::prost::DecodeError> {
                <() as ::autoproto::Proto>::merge_self(&mut (), wire_type, buf, ctx)
            }
        }

        impl #impl_generics ::autoproto::prost::Message for #ident #ty_generics #where_clause {
            fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
            where
                __Buffer: prost::bytes::BufMut,
            {
                <() as ::autoproto::prost::Message>::encode_raw(&(), buf)
            }

            fn merge_field<__Buffer: prost::bytes::Buf>(
                &mut self,
                tag: u32,
                wire_type: ::autoproto::prost::encoding::WireType,
                buf: &mut __Buffer,
                ctx: ::autoproto::prost::encoding::DecodeContext,
            ) -> Result<(), ::autoproto::prost::DecodeError> {
                <() as ::autoproto::prost::Message>::merge_field(&mut (), tag, wire_type, buf, ctx)
            }

            fn encoded_len(&self) -> usize {
                <() as ::autoproto::prost::Message>::encoded_len(&())
            }

            fn clear(&mut self) {
                <() as ::autoproto::prost::Message>::clear(&mut ())
            }
        }
    )
}

struct FieldAttributes {
    tag: Option<NonZeroU32>,
}

impl FieldAttributes {
    fn new(attrs: &[Attribute]) -> Result<Self> {
        let mut tag = None::<NonZeroU32>;

        for attr in attrs {
            match attr.parse_meta()? {
                Meta::NameValue(inner) => {
                    let ident = if let Some(ident) = inner.path.get_ident() {
                        ident
                    } else {
                        continue;
                    };

                    if ident == "tag" {
                        tag = Some(
                            NonZeroU32::new(match inner.lit {
                                Lit::Str(lit) => lit.value().parse()?,
                                Lit::Int(lit) => lit.base10_parse()?,
                                _ => bail!("Unknown tag type"),
                            })
                            .ok_or_else(|| anyhow!("Tag cannot be zero"))?,
                        );
                    }
                }
                _ => {}
            }
        }

        Ok(Self { tag })
    }
}

struct MessageAttributes {
    transparent: bool,
}

impl MessageAttributes {
    fn new(attrs: &[Attribute]) -> Result<Self> {
        let mut transparent = false;

        for meta in attrs
            .iter()
            .filter_map(|attr| match attr.parse_meta().ok()? {
                Meta::List(MetaList { nested: inner, .. }) => Some(inner),
                _ => None,
            })
            .flatten()
        {
            match meta {
                NestedMeta::Meta(Meta::Path(inner)) => {
                    let ident = if let Some(ident) = inner.get_ident() {
                        ident
                    } else {
                        continue;
                    };

                    if ident == "transparent" {
                        transparent = true;
                    }
                }
                _ => {}
            }
        }

        Ok(Self { transparent })
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
