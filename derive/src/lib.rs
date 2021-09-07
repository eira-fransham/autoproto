#![cfg_attr(feature = "nightly", feature(backtrace))]

extern crate proc_macro;

use anyhow::{anyhow, bail};
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use std::{iter, num::NonZeroU32};
use syn::{
    punctuated::Punctuated, Arm, Attribute, Block, Data, DataEnum, DataStruct, DeriveInput, Expr,
    ExprMatch, Field, Fields, FieldsNamed, FieldsUnnamed, GenericParam, Generics, Ident, ItemConst,
    ItemImpl, ItemStruct, Lit, LitInt, Member, Path, Stmt, Token, Type, TypePath,
};

mod newtype;
mod util;

use util::{FieldAttributes, MessageAttributes, Result, WhereClauseBuilder};

#[proc_macro_derive(Message, attributes(autoproto))]
pub fn derive_message(input: TokenStream) -> TokenStream {
    #[cfg(feature = "nightly")]
    if cfg!(debug_assertions) {
        std::panic::set_hook(Box::new(|_panic_info| {
            eprintln!("{}", std::backtrace::Backtrace::capture());
        }));
    }

    try_derive_message(input).unwrap().into()
}

#[proc_macro_derive(Proto, attributes(autoproto))]
pub fn derive_proto(input: TokenStream) -> TokenStream {
    try_derive_proto(input).unwrap().into()
}

#[proc_macro_derive(ProtoEncode, attributes(autoproto))]
pub fn derive_protoencode(input: TokenStream) -> TokenStream {
    try_derive_protoencode(input).unwrap().into()
}

#[proc_macro_derive(ProtoScalar, attributes(autoproto))]
pub fn derive_protoscalar(input: TokenStream) -> TokenStream {
    try_derive_protoscalar(input).unwrap().into()
}

#[proc_macro_derive(IsDefault, attributes(autoproto))]
pub fn derive_is_default(input: TokenStream) -> TokenStream {
    try_derive_is_default(input).unwrap().into()
}

fn derive_protoscalar_enum(
    attrs: MessageAttributes,
    ident: &Ident,
    generics: &Generics,
    data: &DataEnum,
) -> Result<TokenStream2> {
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let autoproto_path = &attrs.autoproto_path;

    let variant_constants = data
        .variants
        .iter()
        .enumerate()
        .map::<Result<_>, _>(|(i, variant)| {
            if variant.fields.is_empty() {
                let variant_ident = &variant.ident;

                let const_name = Ident::new(&format!("__TAG_{}", i), variant_ident.span().clone());

                let item: ItemConst = syn::parse_quote!(
                    const #const_name: ::core::primitive::i32 = #ident::#variant_ident as ::core::primitive::i32;
                );

                Ok((const_name, variant_ident, item))
            } else {
                bail!("Cannot derive `protoscalar` for an enum with fields");
            }
        })
        .collect::<Result<Vec<_>>>()?;

    let constant_items = variant_constants
        .iter()
        .map(|(_, _, item)| item)
        .collect::<Vec<_>>();

    let match_arms = variant_constants
        .iter()
        .map::<Arm, _>(|(const_name, variant_ident, _)| syn::parse_quote!(#const_name => #ident :: #variant_ident))
        .collect::<Punctuated<_, Token!(,)>>();

    let (
        protoscalar_impl,
        is_default_impl,
        protoencode_impl,
        protoencoderepeated_impl,
        protomergerepeated_impl,
        proto_impl,
    ): (ItemImpl, ItemImpl, ItemImpl, ItemImpl, ItemImpl, ItemImpl) = (
        syn::parse_quote!(
            impl #impl_generics #autoproto_path::ProtoScalar for #ident #ty_generics #where_clause {
                const DEFAULT_FIXED: #autoproto_path::Fixed =
                    <::core::primitive::i32 as #autoproto_path::ProtoScalar>::DEFAULT_FIXED;
                const DEFAULT_VARINT: #autoproto_path::Varint =
                    <::core::primitive::i32 as #autoproto_path::ProtoScalar>::DEFAULT_VARINT;
                const DEFAULT_ENCODING: #autoproto_path::ScalarEncoding =
                    <::core::primitive::i32 as #autoproto_path::ProtoScalar>::DEFAULT_ENCODING;

                fn from_value(other: #autoproto_path::Value) -> Option<Self> {
                    ::core::debug_assert_eq!(<Self as ::core::default::Default>::default() as i32, 0);

                    #(#constant_items)*

                    Some(match <::core::primitive::i32 as #autoproto_path::ProtoScalar>::from_value(other)? {
                        #match_arms,
                        _ => return None,
                    })
                }

                fn to_value(&self) -> #autoproto_path::Value {
                    ::core::debug_assert_eq!(<Self as ::core::default::Default>::default() as i32, 0);

                    <::core::primitive::i32 as #autoproto_path::ProtoScalar>::to_value(
                        &(::core::clone::Clone::clone(self) as ::core::primitive::i32)
                    )
                }
            }
        ),
        syn::parse_quote!(
            impl #impl_generics #autoproto_path::IsDefault for #ident #ty_generics #where_clause {
                fn is_default(&self) -> ::core::primitive::bool {
                    (::core::clone::Clone::clone(self) as ::core::primitive::i32) == 0
                }
            }
        ),
        syn::parse_quote!(
            impl #impl_generics #autoproto_path::ProtoEncode for #ident #ty_generics #where_clause {
                fn encode_as_field(
                    &self,
                    tag: ::core::num::NonZeroU32,
                    buf: &mut dyn #autoproto_path::prost::bytes::BufMut,
                ) {
                    <
                        #autoproto_path::MappedInt::<Self>
                        as #autoproto_path::ProtoEncode
                    >::encode_as_field(
                        &#autoproto_path::MappedInt::new(::core::clone::Clone::clone(self)),
                        tag,
                        buf,
                    )
                }

                fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                    <
                        #autoproto_path::MappedInt::<Self>
                        as #autoproto_path::ProtoEncode
                    >::encoded_len_as_field(
                        &#autoproto_path::MappedInt::new(::core::clone::Clone::clone(self)),
                        tag,
                    )
                }
            }
        ),
        syn::parse_quote!(
            impl #impl_generics #autoproto_path::ProtoEncodeRepeated for #ident #ty_generics #where_clause {
                fn encode_as_field_repeated<'__lifetime, I>(
                    iter: I,
                    tag: ::core::num::NonZeroU32,
                    buf: &mut dyn #autoproto_path::bytes::BufMut,
                )
                where
                    I: ExactSizeIterator<Item = &'__lifetime Self> + Clone,
                    Self: '__lifetime,
                {
                    #autoproto_path::MappedInt::<Self>::encode_as_field_repeated(
                        iter,
                        tag,
                        buf,
                    );
                }

                fn encoded_len_as_field_repeated<'__lifetime, I>(iter: I, tag: ::core::num::NonZeroU32) -> usize
                where
                    I: ExactSizeIterator<Item = &'__lifetime Self>,
                    Self: '__lifetime,
                {
                    #autoproto_path::MappedInt::<Self>::encoded_len_as_field_repeated(
                        iter,
                        tag,
                    )
                }
        }),
        syn::parse_quote!(
            impl #impl_generics #autoproto_path::ProtoMergeRepeated for #ident #ty_generics #where_clause {
                fn merge_repeated<T>(
                    values: &mut T,
                    wire_type: #autoproto_path::prost::encoding::WireType,
                    buf: &mut dyn #autoproto_path::bytes::Buf,
                    ctx: #autoproto_path::prost::encoding::DecodeContext,
                ) -> Result<(), #autoproto_path::prost::DecodeError>
                where
                    T: std::iter::Extend<Self>,
                {
                    <#autoproto_path::MappedInt::<Self> as #autoproto_path::ProtoMergeRepeated>::merge_repeated(
                        &mut #autoproto_path::MapExtend::new(values, |#autoproto_path::MappedInt(i, _)| i),
                        wire_type,
                        buf,
                        ctx,
                    )
                }
            }
        ),
        syn::parse_quote!(
            impl #impl_generics #autoproto_path::Proto for #ident #ty_generics #where_clause {
                fn merge_self(
                    &mut self,
                    wire_type: #autoproto_path::prost::encoding::WireType,
                    buf: &mut dyn #autoproto_path::prost::bytes::Buf,
                    ctx: #autoproto_path::prost::encoding::DecodeContext,
                ) -> Result<(), #autoproto_path::prost::DecodeError> {
                    let mut mapped = #autoproto_path::MappedInt::<Self>::new(::core::clone::Clone::clone(self));
                    #autoproto_path::Proto::merge_self(&mut mapped, wire_type, buf, ctx)?;

                    *self = mapped.0;

                    Ok(())
                }
            }
        ),
    );

    Ok(quote! {
        #is_default_impl

        #protoscalar_impl

        #protoencode_impl

        #proto_impl

        #protoencoderepeated_impl

        #protomergerepeated_impl
    })
}

fn derive_protoscalar_struct(
    attrs: MessageAttributes,
    ident: &Ident,
    generics: &Generics,
    data: &DataStruct,
) -> Result<TokenStream2> {
    let (impl_generics, ty_generics, _) = generics.split_for_impl();

    let autoproto_path = &attrs.autoproto_path;

    let (inner_field, bracket) = {
        let (fields, bracket): (_, fn(_) -> _) = match data {
            DataStruct {
                fields: Fields::Named(FieldsNamed { named: fields, .. }),
                ..
            } => (fields, |toks| quote!({ #toks })),
            DataStruct {
                fields:
                    Fields::Unnamed(FieldsUnnamed {
                        unnamed: fields, ..
                    }),
                ..
            } => (fields, |toks| quote!(( #toks ))),
            DataStruct {
                fields: Fields::Unit,
                ..
            } => {
                bail!("`ProtoScalar` can only be implemented for `newtype` structs");
            }
        };

        (
            fields.first().ok_or_else(|| anyhow!("Programmer error"))?,
            bracket,
        )
    };

    let field: Member = inner_field
        .ident
        .clone()
        .map(Member::Named)
        .unwrap_or_else(|| Member::Unnamed(0.into()));

    let mut where_clause_builder = WhereClauseBuilder::new(generics);
    let (
        is_default_impl,
        protoscalar_impl,
        protoencode_impl,
        proto_impl,
        protoencoderepeated_impl,
        protomergerepeated_impl,
    ) = (
        newtype::is_default(
            autoproto_path,
            ident,
            &field,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
        newtype::protoscalar(
            autoproto_path,
            ident,
            &field,
            &inner_field.ty,
            bracket,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
        newtype::protoencode(
            autoproto_path,
            ident,
            &field,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
        newtype::proto(
            autoproto_path,
            ident,
            &field,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
        newtype::protoencoderepeated(
            autoproto_path,
            ident,
            &field,
            &inner_field.ty,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
        newtype::protomergerepeated(
            autoproto_path,
            ident,
            &field,
            &inner_field.ty,
            bracket,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
    );

    Ok(quote! {
        #is_default_impl

        #protoscalar_impl

        #protoencode_impl

        #proto_impl

        #protoencoderepeated_impl

        #protomergerepeated_impl
    })
}

fn try_derive_protoscalar(input: TokenStream) -> Result<TokenStream2> {
    let input: DeriveInput = syn::parse(input)?;
    let DeriveInput {
        attrs,
        vis: _,
        ident,
        generics,
        data,
    } = &input;

    let attrs = MessageAttributes::new(attrs)?;

    match data {
        Data::Struct(data) => derive_protoscalar_struct(attrs, ident, generics, data),
        Data::Enum(data) => derive_protoscalar_enum(attrs, ident, generics, data),
        Data::Union(_) => bail!("Cannot derive `ProtoScalar` for an untagged union"),
    }
}

fn try_derive_is_default(input: TokenStream) -> Result<TokenStream2> {
    let input: DeriveInput = syn::parse(input)?;
    let DeriveInput {
        attrs,
        vis: _,
        ident,
        generics,
        data,
    } = &input;

    let attrs = MessageAttributes::new(attrs)?;

    let (impl_generics, ty_generics, _) = generics.split_for_impl();
    if attrs.transparent {
        let inner_field = match data {
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
                if fields.len() != 1 {
                    bail!("`transparent` message must have exactly one field");
                }

                fields.first().ok_or_else(|| anyhow!("Programmer error"))?
            }
            Data::Struct(DataStruct {
                fields: Fields::Unit,
                ..
            }) => {
                bail!("Cannot have a `transparent` message without fields");
            }
            _ => {
                bail!("Invalid type for a `transparent` message");
            }
        };

        let field: Member = inner_field
            .ident
            .clone()
            .map(Member::Named)
            .unwrap_or_else(|| Member::Unnamed(0.into()));

        let mut where_clause_builder = WhereClauseBuilder::new(generics);
        let is_default_impl = newtype::is_default(
            &attrs.autoproto_path,
            ident,
            &field,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        );

        Ok(quote! { #is_default_impl })
    } else {
        let where_clause_builder = WhereClauseBuilder::new(&generics);
        let where_clause = where_clause_builder
            .with_self_bound(quote!(::core::default::Default + ::core::cmp::PartialEq));

        let autoproto_path = &attrs.autoproto_path;

        Ok(quote! {
            impl #impl_generics #autoproto_path::IsDefault for #ident #ty_generics
            #where_clause
            {
                fn is_default(&self) -> bool {
                    #autoproto_path::generic::default::is_default(self)
                }
            }
        })
    }
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

    let attrs = MessageAttributes::new(attrs)?;

    let autoproto_path = &attrs.autoproto_path;

    if attrs.transparent {
        let inner_field = match data {
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
                if fields.len() != 1 {
                    bail!("`transparent` message must have exactly one field");
                }

                fields.first().ok_or_else(|| anyhow!("Programmer error"))?
            }
            Data::Struct(DataStruct {
                fields: Fields::Unit,
                ..
            }) => {
                bail!("Cannot have a `transparent` message without fields");
            }
            _ => {
                bail!("Invalid type for a `transparent` message");
            }
        };

        let (impl_generics, ty_generics, _) = generics.split_for_impl();
        let field: Member = inner_field
            .ident
            .clone()
            .map(Member::Named)
            .unwrap_or_else(|| Member::Unnamed(0.into()));

        let mut where_clause_builder = WhereClauseBuilder::new(generics);
        let protoencode_impl = newtype::protoencode(
            &attrs.autoproto_path,
            ident,
            &field,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        );

        Ok(quote! { #protoencode_impl })
    } else {
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
                    autoproto_path,
                    fields.into_iter(),
                    ident,
                    generics,
                    DeriveMode::ImmutableOnly,
                )?;

                let (impl_generics, ty_generics, _) = generics.split_for_impl();

                let protoencode_impl = impl_protoencode_for_protostruct(
                    autoproto_path,
                    ident,
                    &impl_generics,
                    &ty_generics,
                    &mut WhereClauseBuilder::new(generics),
                );

                Ok(quote!(
                    #protostruct_impl
                    #protoencode_impl
                ))
            }
            Data::Union(..) => {
                bail!("Message can not be derived for an untagged union (try using `enum`)")
            }
            _ => {
                bail!("Currently unsupported type for `derive(ProtoEncode)`")
            }
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
        Data::Struct(data) => try_derive_message_for_struct(attrs, ident, generics, data),
        Data::Enum(data) => try_derive_oneof(attrs, ident, generics, data),
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
        Data::Struct(data) => try_derive_proto_for_struct(attrs, ident, generics, data),
        Data::Enum(..) => todo!(),
        Data::Union(..) => {
            bail!("Message can not be derived for an untagged union (try using `enum`)")
        }
    }
}

fn try_derive_oneof(
    attrs: &[Attribute],
    ident: &Ident,
    generics: &Generics,
    data: &DataEnum,
) -> Result<TokenStream2> {
    fn make_variant_get_field_arm_with_fields<F, T, FIter>(
        autoproto_path: &Path,
        ident: &Ident,
        tag: &Lit,
        generics: &Generics,
        mut brackets: F,
        semicolon: Option<Token!(;)>,
        fields: &FIter,
    ) -> Arm
    where
        F: FnMut(TokenStream2) -> T,
        T: ToTokens,
        for<'a> &'a FIter: IntoIterator<Item = &'a Field>,
    {
        let names = fields
            .into_iter()
            .enumerate()
            .map(|(i, field)| {
                field
                    .ident
                    .clone()
                    .unwrap_or_else(|| Ident::new(&format!("__field_{}", i), Span::call_site()))
            })
            .collect::<Punctuated<_, Token!(,)>>();

        let make_refs = names
            .iter()
            .map::<Expr, _>(|name| syn::parse_quote!(#autoproto_path::generic::Wrapper(#name)))
            .collect::<Punctuated<_, Token!(,)>>();

        let make_refs: Stmt = syn::parse_quote!(let (#names) = (#make_refs););

        let (typarams, dummy_fields): (Vec<Ident>, Punctuated<_, Token!(,)>) = fields
            .into_iter()
            .cloned()
            .enumerate()
            .map(|(i, field)| {
                let tyident = Ident::new(&format!("__Ty{}", i), Span::call_site());
                let ty = Type::Path(TypePath {
                    qself: None,
                    path: tyident.clone().into(),
                });

                (tyident, Field { ty, ..field })
            })
            .unzip();

        let dummy_generics = Generics {
            params: typarams
                .into_iter()
                .map(|name| GenericParam::Type(name.into()))
                .collect(),
            where_clause: None,
            ..generics.clone()
        };

        let struct_body = brackets(quote!(#dummy_fields));
        let variant_bindings = brackets(quote!(#names));

        syn::parse_quote!(
            Self::#ident #variant_bindings => {
                #[derive(#autoproto_path::ProtoEncode)]
                struct #ident #dummy_generics #struct_body #semicolon

                #make_refs

                __proto_arg_func(
                    &#ident #variant_bindings,
                    unsafe { ::core::num::NonZeroU32::new_unchecked(#tag) },
                )
            }
        )
    }

    fn make_unit_variant_get_field_arm<T: ToTokens>(ident: &Ident, tag: &Lit, brackets: T) -> Arm {
        syn::parse_quote!(
            Self::#ident #brackets => __proto_arg_func(
                &(),
                unsafe { ::core::num::NonZeroU32::new_unchecked(#tag) },
            )
        )
    }

    fn make_newtype_variant_get_field_arm<F, T>(
        ident: &Ident,
        tag: &Lit,
        field_name: Ident,
        brackets: F,
    ) -> Arm
    where
        F: FnOnce(TokenStream2) -> T,
        T: ToTokens,
    {
        let field_name_pat = brackets(quote!(#field_name));

        syn::parse_quote!(
            Self::#ident #field_name_pat => __proto_arg_func(
                #field_name,
                unsafe { ::core::num::NonZeroU32::new_unchecked(#tag) },
            )
        )
    }

    fn make_variant_get_field_arm(
        autoproto_path: &Path,
        ident: &Ident,
        tag: &Lit,
        generics: &Generics,
        fields: &Fields,
    ) -> Arm {
        match &fields {
            Fields::Named(FieldsNamed { named: fields, .. }) => match fields.len() {
                0 => make_unit_variant_get_field_arm(ident, tag, quote!({})),
                1 => {
                    let field_name = fields
                        .first()
                        .and_then(|field| field.ident.clone())
                        .expect("Programmer error: names array should have one named element");

                    make_newtype_variant_get_field_arm(ident, tag, field_name, |f| quote!( { #f } ))
                }
                _ => make_variant_get_field_arm_with_fields(
                    autoproto_path,
                    ident,
                    tag,
                    generics,
                    |val| quote!( { #val } ),
                    None,
                    fields,
                ),
            },
            Fields::Unnamed(FieldsUnnamed {
                unnamed: fields, ..
            }) => match fields.len() {
                0 => make_unit_variant_get_field_arm(ident, tag, quote!(())),
                1 => {
                    let field_name = Ident::new("__proto_enum_inner", Span::call_site());

                    make_newtype_variant_get_field_arm(ident, tag, field_name, |f| quote!( ( #f ) ))
                }
                _ => make_variant_get_field_arm_with_fields(
                    autoproto_path,
                    ident,
                    tag,
                    generics,
                    |val| quote!( ( #val ) ),
                    Some(Default::default()),
                    fields,
                ),
            },
            Fields::Unit => make_unit_variant_get_field_arm(ident, tag, quote!()),
        }
    }

    fn make_variant_exec_merge_arm_with_fields<F, T, FIter>(
        autoproto_path: &Path,
        ident: &Ident,
        tag: &Lit,
        generics: &Generics,
        mut brackets: F,
        semicolon: Option<Token!(;)>,
        fields: &FIter,
    ) -> Arm
    where
        F: FnMut(TokenStream2) -> T,
        T: ToTokens,
        for<'a> &'a FIter: IntoIterator<Item = &'a Field>,
    {
        let names = fields
            .into_iter()
            .enumerate()
            .map(|(i, field)| {
                field
                    .ident
                    .clone()
                    .unwrap_or_else(|| Ident::new(&format!("__field_{}", i), Span::call_site()))
            })
            .collect::<Punctuated<_, Token!(,)>>();

        let (typarams, dummy_fields): (Vec<Ident>, Punctuated<_, Token!(,)>) = fields
            .into_iter()
            .cloned()
            .enumerate()
            .map(|(i, field)| {
                let tyident = Ident::new(&format!("__Ty{}", i), Span::call_site());
                let ty = Type::Path(TypePath {
                    qself: None,
                    path: tyident.clone().into(),
                });

                (tyident, Field { ty, ..field })
            })
            .unzip();

        let dummy_generics = Generics {
            params: typarams
                .into_iter()
                .map(|name| GenericParam::Type(name.into()))
                .collect(),
            where_clause: None,
            ..generics.clone()
        };

        let struct_body = brackets(quote!(
            #dummy_fields,
        ));
        let ref_mut_construct: Stmt = {
            let construct = names
                .iter()
                .map::<Expr, _>(|name| syn::parse_quote!(#autoproto_path::generic::Wrapper(#name)))
                .collect::<Punctuated<_, Token!(,)>>();
            syn::parse_quote!(let (#names) = (#construct);)
        };
        let owned_construct: Stmt = {
            let default: Expr = syn::parse_quote!(::core::default::Default::default());

            let construct = names
                .iter()
                .map(|_| default.clone())
                .collect::<Punctuated<_, Token!(,)>>();
            syn::parse_quote!(let (#names) = (#construct);)
        };
        let variant_bindings = brackets(quote!(#names));

        let (dummy_impl_generics, dummy_ty_generics, _) = dummy_generics.split_for_impl();

        let where_clause_builder = WhereClauseBuilder::new(&dummy_generics);
        let clear_where_clause = where_clause_builder.with_bound(quote!(#autoproto_path::Clear));

        let deconstruct_dummy = brackets(quote!(#names));

        let clear_all = Block {
            brace_token: syn::token::Brace {
                span: Span::call_site(),
            },
            stmts: names
                .iter()
                .map::<Stmt, _>(|name| syn::parse_quote!(#autoproto_path::Clear::clear(#name);))
                .collect(),
        };

        let (dummy_struct_def, dummy_clear_impl): (ItemStruct, ItemImpl) = (
            syn::parse_quote!(
                #[derive(#autoproto_path::Proto)]
                struct #ident #dummy_generics #struct_body #semicolon
            ),
            syn::parse_quote!(
                impl #dummy_impl_generics #autoproto_path::Clear for #ident #dummy_ty_generics
                #clear_where_clause
                {
                    fn clear(&mut self)  {
                        let Self #deconstruct_dummy = self;

                        #clear_all
                    }
                }
            ),
        );

        syn::parse_quote!(
            #tag => {
                #dummy_struct_def

                #dummy_clear_impl

                match self {
                    Self :: #ident #variant_bindings => {
                        #ref_mut_construct

                        let mut __proto_dummy_struct = #ident #variant_bindings;

                        __proto_arg_func(&mut __proto_dummy_struct)
                    }
                    _ => {
                        #owned_construct

                        let mut __proto_dummy_struct = #ident #variant_bindings;

                        let out = __proto_arg_func(&mut __proto_dummy_struct);

                        let #ident #deconstruct_dummy = __proto_dummy_struct;

                        *self = Self::#ident #variant_bindings;

                        out
                    }
                }
            }
        )
    }

    fn make_unit_variant_exec_merge_arm(tag: &Lit) -> Arm {
        syn::parse_quote!(
            #tag => __proto_arg_func(&mut ())
        )
    }

    fn make_newtype_variant_exec_merge_arm<F, T>(
        ident: &Ident,
        tag: &Lit,
        field_name: Option<Ident>,
        brackets: F,
    ) -> Arm
    where
        F: FnOnce(TokenStream2) -> T,
        T: ToTokens,
    {
        let name = Ident::new("__proto_new_inner", Span::call_site());

        let field_spec = field_name.map(|name| quote!(#name :));

        let construct_variant = brackets(quote!(#field_spec #name));

        syn::parse_quote!(
            #tag => {
                let mut #name = Default::default();

                let out = __proto_arg_func(&mut #name);

                *self = Self::#ident #construct_variant;

                out
            }
        )
    }

    fn make_variant_exec_merge_arm(
        autoproto_path: &Path,
        ident: &Ident,
        tag: &Lit,
        generics: &Generics,
        fields: &Fields,
    ) -> Arm {
        match &fields {
            Fields::Named(FieldsNamed { named: fields, .. }) => match fields.len() {
                0 => make_unit_variant_exec_merge_arm(tag),
                1 => {
                    let field_name = fields
                        .first()
                        .and_then(|field| field.ident.clone())
                        .expect("Programmer error: names array should have one named element");

                    make_newtype_variant_exec_merge_arm(
                        ident,
                        tag,
                        Some(field_name),
                        |f| quote!( { #f } ),
                    )
                }
                _ => make_variant_exec_merge_arm_with_fields(
                    autoproto_path,
                    ident,
                    tag,
                    generics,
                    |val| quote!( { #val } ),
                    None,
                    fields,
                ),
            },
            Fields::Unnamed(FieldsUnnamed {
                unnamed: fields, ..
            }) => match fields.len() {
                0 => make_unit_variant_exec_merge_arm(tag),
                1 => make_newtype_variant_exec_merge_arm(ident, tag, None, |f| quote!( ( #f ) )),
                _ => make_variant_exec_merge_arm_with_fields(
                    autoproto_path,
                    ident,
                    tag,
                    generics,
                    |val| quote!( ( #val ) ),
                    Some(Default::default()),
                    fields,
                ),
            },
            Fields::Unit => make_unit_variant_exec_merge_arm(tag),
        }
    }

    let attrs = MessageAttributes::new(attrs)?;

    let autoproto_path = &attrs.autoproto_path;

    let mut explicitly_tagged = None::<bool>;

    let variants = data
        .variants
        .iter()
        .enumerate()
        .map(|(i, variant)| {
            let attributes = FieldAttributes::new(&variant.attrs)?;

            match (explicitly_tagged, &attributes.tag) {
                (None, _) | (Some(true), Some(_)) | (Some(false), None) => {}
                (Some(true), None) | (Some(false), Some(_)) => {
                    return Err(anyhow!(
                        "If `tag` is specified for one field it must be specified for all fields"
                    ));
                }
            }

            explicitly_tagged = Some(attributes.tag.is_some());

            let tag = attributes
                .tag
                .unwrap_or_else(|| NonZeroU32::new(i as u32 + 1).unwrap());
            let tag: Lit = LitInt::new(&tag.get().to_string(), Span::call_site()).into();

            Ok((tag, variant))
        })
        .collect::<Result<Vec<_>>>()?;

    let (impl_generics, ty_generics, _) = generics.split_for_impl();

    let variant_get_field: Vec<Arm> = variants
        .iter()
        .map::<Arm, _>(|(tag, variant)| {
            make_variant_get_field_arm(
                autoproto_path,
                &variant.ident,
                tag,
                generics,
                &variant.fields,
            )
        })
        .collect();

    let variant_exec_merge: Vec<Arm> = variants
        .iter()
        .map::<Arm, _>(|(tag, variant)| {
            make_variant_exec_merge_arm(
                autoproto_path,
                &variant.ident,
                tag,
                generics,
                &variant.fields,
            )
        })
        .chain(iter::once(
            syn::parse_quote!(_ => { return ::core::option::Option::<__FuncOut>::None; }),
        ))
        .collect();

    let where_clause_builder = WhereClauseBuilder::new(generics).with_field_types(
        data.variants
            .iter()
            .filter_map(|v| match &v.fields {
                Fields::Named(FieldsNamed { named: fields, .. })
                | Fields::Unnamed(FieldsUnnamed {
                    unnamed: fields, ..
                }) => Some(fields),
                Fields::Unit => None,
            })
            .flatten()
            .map(|field| &field.ty),
    );

    let get_variant = ExprMatch {
        attrs: vec![],
        match_token: Default::default(),
        expr: syn::parse_quote!(self),
        brace_token: Default::default(),
        arms: variant_get_field,
    };

    let exec_merge = ExprMatch {
        attrs: vec![],
        match_token: Default::default(),
        expr: syn::parse_quote!(::core::num::NonZeroU32::get(tag)),
        brace_token: Default::default(),
        arms: variant_exec_merge,
    };

    let message_where_clause = where_clause_builder
        .with_field_bound(quote!(::core::marker::Send + ::core::marker::Sync))
        .with_self_bound(quote!(
            #autoproto_path::ProtoOneof
                + #autoproto_path::Clear
                + ::core::fmt::Debug
                + ::core::marker::Send
                + ::core::marker::Sync
        ));
    let message_impl = impl_message_for_protooneof(
        autoproto_path,
        ident,
        &impl_generics,
        &ty_generics,
        Some(&message_where_clause),
    );

    let protooneof_where_clause = where_clause_builder.with_field_bound(quote!(
        ::core::default::Default + #autoproto_path::Proto + #autoproto_path::Clear
    ));

    Ok(quote!(
        impl #impl_generics #autoproto_path::ProtoOneof for #ident #ty_generics
        #protooneof_where_clause
        {
            fn variant<__Func, __FuncOut>(&self, __proto_arg_func: __Func) -> __FuncOut
            where
                __Func: ::core::ops::FnOnce(&(dyn #autoproto_path::ProtoEncode + '_), ::core::num::NonZeroU32) -> __FuncOut
            {
                #get_variant
            }

            fn exec_merge<__Func, __FuncOut>(&mut self, tag: ::core::num::NonZeroU32, __proto_arg_func: __Func) -> Option<__FuncOut>
            where
                __Func: ::core::ops::FnOnce(&mut (dyn #autoproto_path::Proto + '_)) -> __FuncOut
            {
                ::core::option::Option::<__FuncOut>::Some(#exec_merge)
            }
        }

        impl #impl_generics #autoproto_path::IsMessage for #ident #ty_generics #protooneof_where_clause {}

        #message_impl
    ))
}

fn try_derive_protostruct<'a>(
    autoproto_path: &Path,
    fields: impl ExactSizeIterator<Item = &'a Field> + Clone,
    ident: &Ident,
    generics: &Generics,
    mode: DeriveMode,
) -> Result<TokenStream2> {
    let (impl_generics, ty_generics, _) = generics.split_for_impl();

    let num_fields = fields.len();

    let mut explicitly_tagged = None::<bool>;

    let members: Result<Vec<(NonZeroU32, Member)>> = fields
        .clone()
        .enumerate()
        .map(|(i, field)| {
            let attributes = FieldAttributes::new(&field.attrs)?;

            match (explicitly_tagged, &attributes.tag) {
                (None, _) | (Some(true), Some(_)) | (Some(false), None) => {}
                (Some(true), None) | (Some(false), Some(_)) => {
                    return Err(anyhow!(
                        "If `tag` is specified for one field it must be specified for all fields"
                    ));
                }
            }

            explicitly_tagged = Some(attributes.tag.is_some());

            Ok((
                attributes
                    .tag
                    .unwrap_or_else(|| NonZeroU32::new(i as u32 + 1).unwrap()),
                field
                    .ident
                    .clone()
                    .map(Member::Named)
                    .unwrap_or_else(|| Member::Unnamed(i.into())),
            ))
        })
        .collect();
    let members = members?;

    let members_array: Punctuated<_, Token!(,)> = members
        .iter()
        .map(|(tag, member)| {
            let tag: Lit = LitInt::new(&tag.get().to_string(), Span::call_site()).into();

            quote!(
                (
                    unsafe { ::core::num::NonZeroU32::new_unchecked(#tag) },
                    &self.#member as &dyn #autoproto_path::ProtoEncode,
                )
            )
        })
        .collect();

    let get_field_mut: Punctuated<_, Token!(,)> = members
        .into_iter()
        .map::<Arm, _>(|(tag, member)| {
            let tag: Lit = LitInt::new(&tag.get().to_string(), Span::call_site()).into();

            syn::parse_quote!(#tag => &mut self.#member)
        })
        .chain(iter::once(syn::parse_quote!(_ => { return None; })))
        .collect();

    let where_clause_builder =
        WhereClauseBuilder::new(generics).with_field_types(fields.map(|f| &f.ty));

    let protostruct_where_clause =
        where_clause_builder.with_field_bound(quote!(#autoproto_path::ProtoEncode));
    let protostructmut_where_clause = where_clause_builder
        .with_field_bound(quote!(#autoproto_path::Proto))
        .with_self_bound(quote!(#autoproto_path::ProtoStruct));

    let immut: ItemImpl = syn::parse_quote! {
        impl #impl_generics #autoproto_path::ProtoStruct for #ident #ty_generics #protostruct_where_clause {
            type Fields<'__field_lifetime>
            where
                Self: '__field_lifetime
            = [
                (
                    ::core::num::NonZeroU32,
                    &'__field_lifetime (dyn #autoproto_path::ProtoEncode + '__field_lifetime),
                );
                #num_fields
            ];

            fn fields(&self) -> Self::Fields<'_> {
                [#members_array]
            }
        }
    };
    let mutable: Option<ItemImpl> = match mode {
        DeriveMode::ImmutableOnly => None,
        DeriveMode::ImmutableAndMutable => Some(syn::parse_quote! {
            impl #impl_generics #autoproto_path::ProtoStructMut for #ident #ty_generics
            #protostructmut_where_clause
            {
                fn field_mut(&mut self, tag: ::core::num::NonZeroU32) -> Option<&mut dyn #autoproto_path::Proto> {
                    Some(match ::core::num::NonZeroU32::get(tag) {
                        #get_field_mut
                    })
                }
            }
        }),
    };

    Ok(quote! {
        impl #impl_generics #autoproto_path::IsMessage for #ident #ty_generics #protostruct_where_clause {}

        #immut

        #mutable
    })
}

fn try_derive_proto_for_struct(
    attrs: &[Attribute],
    ident: &Ident,
    generics: &Generics,
    data: &DataStruct,
) -> Result<TokenStream2> {
    let attrs = MessageAttributes::new(attrs)?;

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let mut where_clause_builder = WhereClauseBuilder::new(generics);

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
                if fields.len() != 1 {
                    bail!("`transparent` message must have exactly one field");
                }

                fields.first().ok_or_else(|| anyhow!("Programmer error"))?
            }
            DataStruct {
                fields: Fields::Unit,
                ..
            } => {
                bail!("Cannot have a `transparent` message without fields");
            }
        };

        let field: Member = inner_field
            .ident
            .clone()
            .map(Member::Named)
            .unwrap_or_else(|| Member::Unnamed(0.into()));

        let mut where_clause_builder = WhereClauseBuilder::new(generics);

        let (protoencode_impl, proto_impl) = (
            newtype::protoencode(
                &attrs.autoproto_path,
                ident,
                &field,
                &impl_generics,
                &ty_generics,
                &mut where_clause_builder,
            ),
            newtype::proto(
                &attrs.autoproto_path,
                ident,
                &field,
                &impl_generics,
                &ty_generics,
                &mut where_clause_builder,
            ),
        );

        Ok(quote! {
            #protoencode_impl
            #proto_impl
        })
    } else {
        let autoproto_path = &attrs.autoproto_path;

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
                        autoproto_path,
                        ident,
                        impl_generics,
                        ty_generics,
                        where_clause,
                    ))
                } else {
                    let protostruct_impl = try_derive_protostruct(
                        autoproto_path,
                        fields.into_iter(),
                        ident,
                        generics,
                        Default::default(),
                    )?;

                    let proto_impl = impl_proto_for_protostruct(
                        autoproto_path,
                        ident,
                        &impl_generics,
                        &ty_generics,
                        &mut where_clause_builder,
                    );

                    Ok(quote!(
                        #protostruct_impl

                        #proto_impl
                    ))
                }
            }
            DataStruct {
                fields: Fields::Unit,
                ..
            } => Ok(unit_proto_impl(
                autoproto_path,
                ident,
                impl_generics,
                ty_generics,
                where_clause,
            )),
        }
    }
}

fn try_derive_message_for_struct(
    attrs: &[Attribute],
    ident: &Ident,
    generics: &Generics,
    data: &DataStruct,
) -> Result<TokenStream2> {
    let attrs = MessageAttributes::new(attrs)?;

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let autoproto_path = &attrs.autoproto_path;

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
                if fields.len() != 1 {
                    bail!("`transparent` message must have exactly one field");
                }

                fields.first().ok_or_else(|| anyhow!("Programmer error"))?
            }
            DataStruct {
                fields: Fields::Unit,
                ..
            } => {
                bail!("Cannot have a `transparent` message without fields");
            }
        };

        let field: Member = inner_field
            .ident
            .clone()
            .map(Member::Named)
            .unwrap_or_else(|| Member::Unnamed(0.into()));

        let mut where_clause_builder = WhereClauseBuilder::new(generics);

        let (protoencode_impl, proto_impl, message_impl) = (
            newtype::protoencode(
                &attrs.autoproto_path,
                ident,
                &field,
                &impl_generics,
                &ty_generics,
                &mut where_clause_builder,
            ),
            newtype::proto(
                &attrs.autoproto_path,
                ident,
                &field,
                &impl_generics,
                &ty_generics,
                &mut where_clause_builder,
            ),
            newtype::message(
                &attrs.autoproto_path,
                ident,
                &field,
                &impl_generics,
                &ty_generics,
                &mut where_clause_builder,
            ),
        );

        Ok(quote! {
            #protoencode_impl
            #proto_impl
            #message_impl
        })
    } else {
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
                        autoproto_path,
                        ident,
                        impl_generics,
                        ty_generics,
                        where_clause,
                    ))
                } else {
                    let where_clause_builder = WhereClauseBuilder::new(generics)
                        .with_field_types(fields.iter().map(|f| &f.ty));

                    let protostruct_impl = try_derive_protostruct(
                        autoproto_path,
                        fields.into_iter(),
                        ident,
                        generics,
                        Default::default(),
                    )?;

                    let message_where_clause = where_clause_builder
                        .with_field_bound(quote!(::core::marker::Send + ::core::marker::Sync))
                        .with_self_bound(quote!(
                            #autoproto_path::ProtoStructMut
                                + #autoproto_path::Clear
                                + ::core::fmt::Debug
                                + ::core::marker::Send
                                + ::core::marker::Sync
                        ));
                    let message_impl = impl_message_for_protostruct(
                        autoproto_path,
                        ident,
                        &impl_generics,
                        &ty_generics,
                        Some(&message_where_clause),
                    );

                    Ok(quote!(
                        #protostruct_impl

                        #message_impl
                    ))
                }
            }
            DataStruct {
                fields: Fields::Unit,
                ..
            } => Ok(unit_proto_impl(
                autoproto_path,
                ident,
                impl_generics,
                ty_generics,
                where_clause,
            )),
        }
    }
}

fn impl_message_for_protooneof(
    autoproto_path: &Path,
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> ItemImpl {
    syn::parse_quote!(
        impl #impl_generics #autoproto_path::prost::Message for #ident #ty_generics #where_clause
        {
            fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
            where
                __Buffer: #autoproto_path::prost::bytes::BufMut,
            {
                #autoproto_path::generic::protooneof::message_encode_raw(self, buf)
            }

            fn merge_field<__Buffer: #autoproto_path::prost::bytes::Buf>(
                &mut self,
                tag: u32,
                wire_type: #autoproto_path::prost::encoding::WireType,
                buf: &mut __Buffer,
                ctx: #autoproto_path::prost::encoding::DecodeContext,
            ) -> Result<(), #autoproto_path::prost::DecodeError> {
                #autoproto_path::generic::protooneof::message_merge_field(self, tag, wire_type, buf, ctx)
            }

            fn encoded_len(&self) -> usize {
                #autoproto_path::generic::protooneof::message_encoded_len(self)
            }

            fn clear(&mut self) {
                #autoproto_path::generic::clear::message_clear(self)
            }
        }
    )
}

fn impl_message_for_protostruct(
    autoproto_path: &Path,
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> ItemImpl {
    syn::parse_quote!(
        impl #impl_generics #autoproto_path::prost::Message for #ident #ty_generics #where_clause
        {
            fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
            where
                __Buffer: #autoproto_path::prost::bytes::BufMut,
            {
                #autoproto_path::generic::protostruct::message_encode_raw(self, buf)
            }

            fn merge_field<__Buffer: #autoproto_path::prost::bytes::Buf>(
                &mut self,
                tag: u32,
                wire_type: #autoproto_path::prost::encoding::WireType,
                buf: &mut __Buffer,
                ctx: #autoproto_path::prost::encoding::DecodeContext,
            ) -> Result<(), #autoproto_path::prost::DecodeError> {
                #autoproto_path::generic::protostruct::message_merge_field(self, tag, wire_type, buf, ctx)
            }

            fn encoded_len(&self) -> usize {
                #autoproto_path::generic::protostruct::message_encoded_len(self)
            }

            fn clear(&mut self) {
                #autoproto_path::generic::clear::message_clear(self)
            }
        }
    )
}

fn impl_proto_for_protostruct(
    autoproto_path: &Path,
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> TokenStream2 {
    let protoencode_impl = impl_protoencode_for_protostruct(
        autoproto_path,
        ident,
        impl_generics,
        ty_generics,
        where_clause_builder,
    );
    let proto_where_clause = where_clause_builder.build().with_self_bound(quote!(
        #autoproto_path::ProtoStructMut + #autoproto_path::ProtoEncode + #autoproto_path::Clear
    ));

    quote!(
        impl #impl_generics #autoproto_path::Proto for #ident #ty_generics #proto_where_clause
        {
            fn merge_self(
                &mut self,
                wire_type: #autoproto_path::prost::encoding::WireType,
                mut buf: &mut dyn #autoproto_path::prost::bytes::Buf,
                ctx: #autoproto_path::prost::encoding::DecodeContext,
            ) -> Result<(), #autoproto_path::prost::DecodeError> {
                #autoproto_path::generic::protostruct::proto_merge_self(self, wire_type, &mut buf, ctx)
            }
        }

        #protoencode_impl
    )
}

fn impl_protoencode_for_protostruct(
    autoproto_path: &Path,
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let where_clause = where_clause_builder.with_self_bound(quote!(#autoproto_path::ProtoStruct));

    syn::parse_quote!(
        impl #impl_generics #autoproto_path::ProtoEncode for #ident #ty_generics #where_clause
        {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, mut buf: &mut dyn #autoproto_path::prost::bytes::BufMut) {
                #autoproto_path::generic::protostruct::protoencode_encode_as_field(self, tag, buf)
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                #autoproto_path::generic::protostruct::protoencode_encoded_len_as_field(self, tag)
            }
        }
    )
}

fn unit_proto_impl(
    autoproto_path: &Path,
    ident: &Ident,
    impl_generics: syn::ImplGenerics,
    ty_generics: syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> TokenStream2 {
    quote!(
        impl #impl_generics #autoproto_path::ProtoEncode for #ident #ty_generics #where_clause {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, buf: &mut dyn prost::bytes::BufMut) {
                <() as #autoproto_path::ProtoEncode>::encode_as_field(&(), tag, buf)
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                <() as #autoproto_path::ProtoEncode>::encoded_len_as_field(&(), tag)
            }
        }

        impl #impl_generics #autoproto_path::Proto for #ident #ty_generics #where_clause {
            fn merge_self(
                &mut self,
                wire_type: #autoproto_path::prost::encoding::WireType,
                buf: &mut dyn #autoproto_path::prost::bytes::Buf,
                ctx: #autoproto_path::prost::encoding::DecodeContext,
            ) -> Result<(), #autoproto_path::prost::DecodeError> {
                <() as #autoproto_path::Proto>::merge_self(&mut (), wire_type, buf, ctx)
            }
        }

        impl #impl_generics #autoproto_path::prost::Message for #ident #ty_generics #where_clause {
            fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
            where
                __Buffer: prost::bytes::BufMut,
            {
                <() as #autoproto_path::prost::Message>::encode_raw(&(), buf)
            }

            fn merge_field<__Buffer: prost::bytes::Buf>(
                &mut self,
                tag: u32,
                wire_type: #autoproto_path::prost::encoding::WireType,
                buf: &mut __Buffer,
                ctx: #autoproto_path::prost::encoding::DecodeContext,
            ) -> Result<(), #autoproto_path::prost::DecodeError> {
                <() as #autoproto_path::prost::Message>::merge_field(&mut (), tag, wire_type, buf, ctx)
            }

            fn encoded_len(&self) -> usize {
                <() as #autoproto_path::prost::Message>::encoded_len(&())
            }

            fn clear(&mut self) {
                <() as #autoproto_path::prost::Message>::clear(&mut ())
            }
        }
    )
}
