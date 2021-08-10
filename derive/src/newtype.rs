use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use syn::{Ident, ItemImpl, Member, Type};

use crate::util::WhereClauseBuilder;

pub fn protoencode(
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let protoencode_where_clause =
        where_clause_builder.with_bound(quote!(::autoproto::ProtoEncode));

    syn::parse_quote!(
        impl #impl_generics ::autoproto::ProtoEncode for #ident #ty_generics #protoencode_where_clause {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, buf: &mut dyn ::autoproto::bytes::BufMut) {
                ::autoproto::ProtoEncode::encode_as_field(&self.#field, tag, buf)
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                ::autoproto::ProtoEncode::encoded_len_as_field(&self.#field, tag)
            }
        }
    )
}

pub fn protoencoderepeated(
    ident: &Ident,
    field: &Member,
    field_ty: &Type,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let protoencoderepeated_where_clause =
        where_clause_builder.with_bound(quote!(::autoproto::ProtoEncodeRepeated));

    syn::parse_quote!(
        impl #impl_generics ::autoproto::ProtoEncodeRepeated for #ident #ty_generics
        #protoencoderepeated_where_clause
        {
            fn encode_as_field_repeated<'a, __I>(iter: __I, tag: ::core::num::NonZeroU32, buf: &mut dyn ::autoproto::bytes::BufMut)
            where
                __I: ExactSizeIterator<Item = &'a Self> + Clone,
                Self: 'a,
            {
                <#field_ty as ::autoproto::ProtoEncodeRepeated>::encode_as_field_repeated(
                    iter.map(|i| &i.#field),
                    tag,
                    buf,
                );
            }

            fn encoded_len_as_field_repeated<'a, __I>(iter: __I, tag: ::core::num::NonZeroU32) -> usize
            where
                __I: ExactSizeIterator<Item = &'a Self>,
                Self: 'a,
            {
                <#field_ty as ::autoproto::ProtoEncodeRepeated>::encoded_len_as_field_repeated(
                    iter.map(|i| &i.#field),
                    tag,
                )
            }
        }
    )
}

pub fn protomergerepeated<F, T>(
    ident: &Ident,
    field: &Member,
    field_ty: &Type,
    mut brackets: F,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl
where
    F: FnMut(TokenStream2) -> T,
    T: ToTokens,
{
    let protomergerepeated_where_clause = where_clause_builder
        .with_bound(quote!(::autoproto::ProtoMergeRepeated))
        .with_self_bound(quote!(::autoproto::Proto + ::core::default::Default));

    let dummy_ident;
    let field_var = match field {
        Member::Named(ident) => ident,
        Member::Unnamed(syn::Index { index, .. }) => {
            dummy_ident = Ident::new(&format!("__field_{}", index), Span::call_site());

            &dummy_ident
        }
    };

    let construct = brackets(quote!(#field_var));

    syn::parse_quote!(
        impl #impl_generics ::autoproto::ProtoMergeRepeated for #ident #ty_generics
        #protomergerepeated_where_clause
        {
            fn merge_repeated<__Extend>(
                values: &mut __Extend,
                wire_type: ::autoproto::prost::encoding::WireType,
                buf: &mut dyn ::autoproto::bytes::Buf,
                ctx: ::autoproto::prost::encoding::DecodeContext,
            ) -> Result<(), ::autoproto::prost::DecodeError>
            where
                __Extend: std::iter::Extend<Self>,
            {
                <#field_ty as ::autoproto::ProtoMergeRepeated>::merge_repeated(
                    &mut ::autoproto::MapExtend::new(values, |#field_var| Self #construct),
                    wire_type,
                    buf,
                    ctx,
                )
            }
        }
    )
}
pub fn proto(
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let proto_where_clause = where_clause_builder.with_bound(quote!(::autoproto::Proto));

    syn::parse_quote!(
        impl #impl_generics ::autoproto::Proto for #ident #ty_generics #proto_where_clause {
            fn merge_self(
                &mut self,
                wire_type: ::autoproto::prost::encoding::WireType,
                buf: &mut dyn ::autoproto::bytes::Buf,
                ctx: ::autoproto::prost::encoding::DecodeContext,
            ) -> Result<(), ::autoproto::prost::DecodeError> {
                ::autoproto::Proto::merge_self(&mut self.#field, wire_type, buf, ctx)
            }
        }
    )
}

pub fn message(
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let message_where_clause = where_clause_builder.with_bound(quote!(::autoproto::prost::Message));

    syn::parse_quote!(
        impl #impl_generics ::autoproto::prost::Message for #ident #ty_generics #message_where_clause {
            fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
            where
                __Buffer: ::autoproto::bytes::BufMut,
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
    )
}

pub fn is_default(
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let is_default_where_clause = where_clause_builder.with_bound(quote!(::autoproto::IsDefault));

    syn::parse_quote!(
        impl #impl_generics ::autoproto::IsDefault for #ident #ty_generics #is_default_where_clause {
            fn is_default(&self) -> bool {
                ::autoproto::IsDefault::is_default(&self.#field)
            }
        }
    )
}

pub fn protoscalar<F, T>(
    ident: &Ident,
    field: &Member,
    field_ty: &Type,
    mut brackets: F,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl
where
    F: FnMut(TokenStream2) -> T,
    T: ToTokens,
{
    let protoscalar_where_clause =
        where_clause_builder.with_bound(quote!(::autoproto::ProtoScalar));

    let dummy_ident;
    let field_var = match field {
        Member::Named(ident) => ident,
        Member::Unnamed(syn::Index { index, .. }) => {
            dummy_ident = Ident::new(&format!("__field_{}", index), Span::call_site());

            &dummy_ident
        }
    };

    let construct = brackets(quote!(#field_var));

    syn::parse_quote!(
        impl #impl_generics ::autoproto::ProtoScalar for #ident #ty_generics #protoscalar_where_clause {
            const DEFAULT_FIXED: ::autoproto::Fixed = <#field_ty as ::autoproto::ProtoScalar>::DEFAULT_FIXED;
            const DEFAULT_VARINT: ::autoproto::Varint = <#field_ty as ::autoproto::ProtoScalar>::DEFAULT_VARINT;
            const DEFAULT_ENCODING: ::autoproto::ScalarEncoding = <#field_ty as ::autoproto::ProtoScalar>::DEFAULT_ENCODING;

            fn from_value(other: ::autoproto::Value) -> Option<Self> {
                <#field_ty as ::autoproto::ProtoScalar>::from_value(other)
                    .map(|#field_var| Self #construct)
            }

            fn to_value(&self) -> ::autoproto::Value {
                ::autoproto::ProtoScalar::to_value(&self.#field)
            }
        }
    )
}
