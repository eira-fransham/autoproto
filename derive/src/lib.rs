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
    ItemImpl, ItemStruct, Lit, LitInt, Member, Stmt, Token, Type, TypePath,
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
    ident: &Ident,
    generics: &Generics,
    data: &DataEnum,
) -> Result<TokenStream2> {
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

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
            impl #impl_generics ::autoproto::ProtoScalar for #ident #ty_generics #where_clause {
                const DEFAULT_FIXED: ::autoproto::Fixed =
                    <::core::primitive::i32 as ::autoproto::ProtoScalar>::DEFAULT_FIXED;
                const DEFAULT_VARINT: ::autoproto::Varint =
                    <::core::primitive::i32 as ::autoproto::ProtoScalar>::DEFAULT_VARINT;
                const DEFAULT_ENCODING: ::autoproto::ScalarEncoding =
                    <::core::primitive::i32 as ::autoproto::ProtoScalar>::DEFAULT_ENCODING;

                fn from_value(other: ::autoproto::Value) -> Option<Self> {
                    ::core::debug_assert_eq!(<Self as ::core::default::Default>::default() as i32, 0);

                    #(#constant_items)*

                    Some(match <::core::primitive::i32 as ::autoproto::ProtoScalar>::from_value(other)? {
                        #match_arms,
                        _ => return None,
                    })
                }

                fn to_value(&self) -> ::autoproto::Value {
                    ::core::debug_assert_eq!(<Self as ::core::default::Default>::default() as i32, 0);

                    <::core::primitive::i32 as ::autoproto::ProtoScalar>::to_value(
                        &(::core::clone::Clone::clone(self) as ::core::primitive::i32)
                    )
                }
            }
        ),
        syn::parse_quote!(
            impl #impl_generics ::autoproto::IsDefault for #ident #ty_generics #where_clause {
                fn is_default(&self) -> ::core::primitive::bool {
                    (::core::clone::Clone::clone(self) as ::core::primitive::i32) == 0
                }
            }
        ),
        syn::parse_quote!(
            impl #impl_generics ::autoproto::ProtoEncode for #ident #ty_generics #where_clause {
                fn encode_as_field(
                    &self,
                    tag: ::core::num::NonZeroU32,
                    buf: &mut dyn ::autoproto::prost::bytes::BufMut,
                ) {
                    <
                        ::autoproto::MappedInt::<Self>
                        as ::autoproto::ProtoEncode
                    >::encode_as_field(
                        &::autoproto::MappedInt::new(::core::clone::Clone::clone(self)),
                        tag,
                        buf,
                    )
                }

                fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                    <
                        ::autoproto::MappedInt::<Self>
                        as ::autoproto::ProtoEncode
                    >::encoded_len_as_field(
                        &::autoproto::MappedInt::new(::core::clone::Clone::clone(self)),
                        tag,
                    )
                }
            }
        ),
        syn::parse_quote!(
            impl #impl_generics ::autoproto::ProtoEncodeRepeated for #ident #ty_generics #where_clause {
                fn encode_as_field_repeated<'__lifetime, I>(
                    iter: I,
                    tag: ::core::num::NonZeroU32,
                    buf: &mut dyn ::autoproto::bytes::BufMut,
                )
                where
                    I: ExactSizeIterator<Item = &'__lifetime Self> + Clone,
                    Self: '__lifetime,
                {
                    ::autoproto::MappedInt::<Self>::encode_as_field_repeated(
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
                    ::autoproto::MappedInt::<Self>::encoded_len_as_field_repeated(
                        iter,
                        tag,
                    )
                }
        }),
        syn::parse_quote!(
            impl #impl_generics ::autoproto::ProtoMergeRepeated for #ident #ty_generics #where_clause {
                fn merge_repeated<T>(
                    values: &mut T,
                    wire_type: ::autoproto::prost::encoding::WireType,
                    buf: &mut dyn ::autoproto::bytes::Buf,
                    ctx: ::autoproto::prost::encoding::DecodeContext,
                ) -> Result<(), ::autoproto::prost::DecodeError>
                where
                    T: std::iter::Extend<Self>,
                {
                    <::autoproto::MappedInt::<Self> as ::autoproto::ProtoMergeRepeated>::merge_repeated(
                        &mut ::autoproto::MapExtend::new(values, |::autoproto::MappedInt(i, _)| i),
                        wire_type,
                        buf,
                        ctx,
                    )
                }
            }
        ),
        syn::parse_quote!(
            impl #impl_generics ::autoproto::Proto for #ident #ty_generics #where_clause {
                fn merge_self(
                    &mut self,
                    wire_type: ::autoproto::prost::encoding::WireType,
                    buf: &mut dyn ::autoproto::prost::bytes::Buf,
                    ctx: ::autoproto::prost::encoding::DecodeContext,
                ) -> Result<(), ::autoproto::prost::DecodeError> {
                    let mut mapped = ::autoproto::MappedInt::<Self>::new(::core::clone::Clone::clone(self));
                    ::autoproto::Proto::merge_self(&mut mapped, wire_type, buf, ctx)?;

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
    ident: &Ident,
    generics: &Generics,
    data: &DataStruct,
) -> Result<TokenStream2> {
    let (impl_generics, ty_generics, _) = generics.split_for_impl();

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
            ident,
            &field,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
        newtype::protoscalar(
            ident,
            &field,
            &inner_field.ty,
            bracket,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
        newtype::protoencode(
            ident,
            &field,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
        newtype::proto(
            ident,
            &field,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
        newtype::protoencoderepeated(
            ident,
            &field,
            &inner_field.ty,
            &impl_generics,
            &ty_generics,
            &mut where_clause_builder,
        ),
        newtype::protomergerepeated(
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
        attrs: _,
        vis: _,
        ident,
        generics,
        data,
    } = &input;

    match data {
        Data::Struct(data) => derive_protoscalar_struct(ident, generics, data),
        Data::Enum(data) => derive_protoscalar_enum(ident, generics, data),
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

        Ok(quote! {
            impl #impl_generics ::autoproto::IsDefault for #ident #ty_generics
            #where_clause
            {
                fn is_default(&self) -> bool {
                    ::autoproto::generic::default::is_default(self)
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
                    fields.into_iter(),
                    ident,
                    generics,
                    DeriveMode::ImmutableOnly,
                )?;

                let (impl_generics, ty_generics, _) = generics.split_for_impl();

                let protoencode_impl = impl_protoencode_for_protostruct(
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
    _attrs: &[Attribute],
    ident: &Ident,
    generics: &Generics,
    data: &DataEnum,
) -> Result<TokenStream2> {
    fn make_variant_get_field_arm_with_fields<F, T, FIter>(
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
            .map::<Expr, _>(|name| syn::parse_quote!(::autoproto::generic::Wrapper(#name)))
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
                #[derive(::autoproto::ProtoEncode)]
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
                .map::<Expr, _>(|name| syn::parse_quote!(::autoproto::generic::Wrapper(#name)))
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
        let clear_where_clause = where_clause_builder.with_bound(quote!(::autoproto::Clear));

        let deconstruct_dummy = brackets(quote!(#names));

        let clear_all = Block {
            brace_token: syn::token::Brace {
                span: Span::call_site(),
            },
            stmts: names
                .iter()
                .map::<Stmt, _>(|name| syn::parse_quote!(::autoproto::Clear::clear(#name);))
                .collect(),
        };

        let (dummy_struct_def, dummy_clear_impl): (ItemStruct, ItemImpl) = (
            syn::parse_quote!(
                #[derive(::autoproto::Proto)]
                struct #ident #dummy_generics #struct_body #semicolon
            ),
            syn::parse_quote!(
                impl #dummy_impl_generics ::autoproto::Clear for #ident #dummy_ty_generics
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
            make_variant_get_field_arm(&variant.ident, tag, generics, &variant.fields)
        })
        .collect();

    let variant_exec_merge: Vec<Arm> = variants
        .iter()
        .map::<Arm, _>(|(tag, variant)| {
            make_variant_exec_merge_arm(&variant.ident, tag, generics, &variant.fields)
        })
        .chain(iter::once(
            syn::parse_quote!(_ => { return ::core::option::Option::<__FuncOut>::None; }),
        ))
        .collect();

    let where_clause_builder = WhereClauseBuilder::new(generics);

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

    let message_where_clause = where_clause_builder.with_self_bound(quote!(
        ::autoproto::ProtoOneof
            + ::autoproto::Clear
            + ::core::fmt::Debug
            + ::core::marker::Send
            + ::core::marker::Sync
    ));
    let message_impl = impl_message_for_protooneof(
        ident,
        &impl_generics,
        &ty_generics,
        Some(&message_where_clause),
    );

    let protooneof_where_clause = where_clause_builder.with_bound(quote!(
        ::core::default::Default + ::autoproto::Proto + ::autoproto::Clear
    ));

    Ok(quote!(
        impl #impl_generics ::autoproto::ProtoOneof for #ident #ty_generics
        #protooneof_where_clause
        {
            fn variant<__Func, __FuncOut>(&self, __proto_arg_func: __Func) -> __FuncOut
            where
                __Func: ::core::ops::FnOnce(&(dyn ::autoproto::ProtoEncode + '_), ::core::num::NonZeroU32) -> __FuncOut
            {
                #get_variant
            }

            fn exec_merge<__Func, __FuncOut>(&mut self, tag: ::core::num::NonZeroU32, __proto_arg_func: __Func) -> Option<__FuncOut>
            where
                __Func: ::core::ops::FnOnce(&mut (dyn ::autoproto::Proto + '_)) -> __FuncOut
            {
                ::core::option::Option::<__FuncOut>::Some(#exec_merge)
            }
        }

        impl #impl_generics ::autoproto::IsMessage for #ident #ty_generics #protooneof_where_clause {}

        #message_impl
    ))
}

fn try_derive_protostruct<'a>(
    fields: impl ExactSizeIterator<Item = &'a Field>,
    ident: &Ident,
    generics: &Generics,
    mode: DeriveMode,
) -> Result<TokenStream2> {
    let (impl_generics, ty_generics, _) = generics.split_for_impl();

    let num_fields = fields.len();

    let mut explicitly_tagged = None::<bool>;

    let fields: Result<Vec<(NonZeroU32, Member)>> = fields
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
    let fields = fields?;

    let fields_array: Punctuated<_, Token!(,)> = fields
        .iter()
        .map(|(tag, member)| {
            let tag: Lit = LitInt::new(&tag.get().to_string(), Span::call_site()).into();

            quote!(
                (
                    unsafe { ::core::num::NonZeroU32::new_unchecked(#tag) },
                    &self.#member as &dyn ::autoproto::ProtoEncode,
                )
            )
        })
        .collect();

    let get_field_mut: Punctuated<_, Token!(,)> = fields
        .into_iter()
        .map::<Arm, _>(|(tag, member)| {
            let tag: Lit = LitInt::new(&tag.get().to_string(), Span::call_site()).into();

            syn::parse_quote!(#tag => &mut self.#member)
        })
        .chain(iter::once(syn::parse_quote!(_ => { return None; })))
        .collect();

    let where_clause_builder = WhereClauseBuilder::new(generics);

    let protostruct_where_clause =
        where_clause_builder.with_bound(quote!(::autoproto::ProtoEncode));
    let protostructmut_where_clause = where_clause_builder
        .with_bound(quote!(::autoproto::Proto))
        .with_self_bound(quote!(::autoproto::ProtoStruct));

    let immut: ItemImpl = syn::parse_quote! {
        impl #impl_generics ::autoproto::ProtoStruct for #ident #ty_generics #protostruct_where_clause {
            type Fields<'__field_lifetime>
            where
                Self: '__field_lifetime
            = [
                (
                    ::core::num::NonZeroU32,
                    &'__field_lifetime (dyn ::autoproto::ProtoEncode + '__field_lifetime),
                );
                #num_fields
            ];

            fn fields(&self) -> Self::Fields<'_> {
                [#fields_array]
            }
        }
    };
    let mutable: Option<ItemImpl> = match mode {
        DeriveMode::ImmutableOnly => None,
        DeriveMode::ImmutableAndMutable => Some(syn::parse_quote! {
            impl #impl_generics ::autoproto::ProtoStructMut for #ident #ty_generics
            #protostructmut_where_clause
            {
                fn field_mut(&mut self, tag: ::core::num::NonZeroU32) -> Option<&mut dyn ::autoproto::Proto> {
                    Some(match ::core::num::NonZeroU32::get(tag) {
                        #get_field_mut
                    })
                }
            }
        }),
    };

    Ok(quote! {
        impl #impl_generics ::autoproto::IsMessage for #ident #ty_generics #protostruct_where_clause {}

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
                ident,
                &field,
                &impl_generics,
                &ty_generics,
                &mut where_clause_builder,
            ),
            newtype::proto(
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

                    let proto_impl = impl_proto_for_protostruct(
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

    let where_clause_builder = WhereClauseBuilder::new(generics);

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
                ident,
                &field,
                &impl_generics,
                &ty_generics,
                &mut where_clause_builder,
            ),
            newtype::proto(
                ident,
                &field,
                &impl_generics,
                &ty_generics,
                &mut where_clause_builder,
            ),
            newtype::message(
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

                    let message_where_clause = where_clause_builder.with_self_bound(quote!(
                        ::autoproto::ProtoStructMut
                            + ::autoproto::Clear
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
                ident,
                impl_generics,
                ty_generics,
                where_clause,
            )),
        }
    }
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
                ::autoproto::generic::clear::message_clear(self)
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
                ::autoproto::generic::clear::message_clear(self)
            }
        }
    )
}

fn impl_proto_for_protostruct(
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> TokenStream2 {
    let protoencode_impl =
        impl_protoencode_for_protostruct(ident, impl_generics, ty_generics, where_clause_builder);
    let proto_where_clause = where_clause_builder.build().with_self_bound(quote!(
        ::autoproto::ProtoStructMut + ::autoproto::ProtoEncode + ::autoproto::Clear
    ));

    quote!(
        impl #impl_generics ::autoproto::Proto for #ident #ty_generics #proto_where_clause
        {
            fn merge_self(
                &mut self,
                wire_type: ::autoproto::prost::encoding::WireType,
                mut buf: &mut dyn ::autoproto::prost::bytes::Buf,
                ctx: ::autoproto::prost::encoding::DecodeContext,
            ) -> Result<(), ::autoproto::prost::DecodeError> {
                ::autoproto::generic::protostruct::proto_merge_self(self, wire_type, &mut buf, ctx)
            }
        }

        #protoencode_impl
    )
}

fn impl_protoencode_for_protostruct(
    ident: &Ident,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let where_clause = where_clause_builder.with_self_bound(quote!(::autoproto::ProtoStruct));

    syn::parse_quote!(
        impl #impl_generics ::autoproto::ProtoEncode for #ident #ty_generics #where_clause
        {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, mut buf: &mut dyn ::autoproto::prost::bytes::BufMut) {
                ::autoproto::generic::protostruct::protoencode_encode_as_field(self, tag, buf)
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                ::autoproto::generic::protostruct::protoencode_encoded_len_as_field(self, tag)
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
