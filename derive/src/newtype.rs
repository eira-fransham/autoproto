use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use syn::{Ident, ItemImpl, Member, Path, Type};

use crate::util::WhereClauseBuilder;

pub fn protoencode(
    autoproto_path: &Path,
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let protoencode_where_clause =
        where_clause_builder.with_bound(quote!(#autoproto_path::ProtoEncode));

    syn::parse_quote!(
        impl #impl_generics #autoproto_path::ProtoEncode for #ident #ty_generics #protoencode_where_clause {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, buf: &mut dyn #autoproto_path::bytes::BufMut) {
                #autoproto_path::ProtoEncode::encode_as_field(&self.#field, tag, buf)
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                #autoproto_path::ProtoEncode::encoded_len_as_field(&self.#field, tag)
            }
        }
    )
}

pub fn protoencoderepeated(
    autoproto_path: &Path,
    ident: &Ident,
    field: &Member,
    field_ty: &Type,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let protoencoderepeated_where_clause =
        where_clause_builder.with_bound(quote!(#autoproto_path::ProtoEncodeRepeated));

    syn::parse_quote!(
        impl #impl_generics #autoproto_path::ProtoEncodeRepeated for #ident #ty_generics
        #protoencoderepeated_where_clause
        {
            fn encode_as_field_repeated<'a, __I>(iter: __I, tag: ::core::num::NonZeroU32, buf: &mut dyn #autoproto_path::bytes::BufMut)
            where
                __I: ExactSizeIterator<Item = &'a Self> + Clone,
                Self: 'a,
            {
                <#field_ty as #autoproto_path::ProtoEncodeRepeated>::encode_as_field_repeated(
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
                <#field_ty as #autoproto_path::ProtoEncodeRepeated>::encoded_len_as_field_repeated(
                    iter.map(|i| &i.#field),
                    tag,
                )
            }
        }
    )
}

pub fn protomergerepeated<F, T>(
    autoproto_path: &Path,
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
        .with_bound(quote!(#autoproto_path::ProtoMergeRepeated))
        .with_self_bound(quote!(#autoproto_path::Proto + ::core::default::Default));

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
        impl #impl_generics #autoproto_path::ProtoMergeRepeated for #ident #ty_generics
        #protomergerepeated_where_clause
        {
            fn merge_repeated<__Extend>(
                values: &mut __Extend,
                wire_type: #autoproto_path::prost::encoding::WireType,
                buf: &mut dyn #autoproto_path::bytes::Buf,
                ctx: #autoproto_path::prost::encoding::DecodeContext,
            ) -> Result<(), #autoproto_path::prost::DecodeError>
            where
                __Extend: std::iter::Extend<Self>,
            {
                <#field_ty as #autoproto_path::ProtoMergeRepeated>::merge_repeated(
                    &mut #autoproto_path::MapExtend::new(values, |#field_var| Self #construct),
                    wire_type,
                    buf,
                    ctx,
                )
            }
        }
    )
}
pub fn proto(
    autoproto_path: &Path,
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let proto_where_clause = where_clause_builder.with_bound(quote!(#autoproto_path::Proto));

    syn::parse_quote!(
        impl #impl_generics #autoproto_path::Proto for #ident #ty_generics #proto_where_clause {
            fn merge_self(
                &mut self,
                wire_type: #autoproto_path::prost::encoding::WireType,
                buf: &mut dyn #autoproto_path::bytes::Buf,
                ctx: #autoproto_path::prost::encoding::DecodeContext,
            ) -> Result<(), #autoproto_path::prost::DecodeError> {
                #autoproto_path::Proto::merge_self(&mut self.#field, wire_type, buf, ctx)
            }
        }
    )
}

pub fn message(
    autoproto_path: &Path,
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let message_where_clause =
        where_clause_builder.with_bound(quote!(#autoproto_path::prost::Message));

    syn::parse_quote!(
        impl #impl_generics #autoproto_path::prost::Message for #ident #ty_generics #message_where_clause {
            fn encode_raw<__Buffer>(&self, buf: &mut __Buffer)
            where
                __Buffer: #autoproto_path::bytes::BufMut,
            {
                #autoproto_path::prost::Message::encode_raw(&self.#field, buf)
            }

            fn merge_field<__Buffer: prost::bytes::Buf>(
                &mut self,
                tag: u32,
                wire_type: #autoproto_path::prost::encoding::WireType,
                buf: &mut __Buffer,
                ctx: #autoproto_path::prost::encoding::DecodeContext,
            ) -> Result<(), #autoproto_path::prost::DecodeError> {
                #autoproto_path::prost::Message::merge_field(&mut self.#field, tag, wire_type, buf, ctx)
            }

            fn encoded_len(&self) -> usize {
                #autoproto_path::prost::Message::encoded_len(&self.#field)
            }

            fn clear(&mut self) {
                #autoproto_path::prost::Message::clear(&mut self.#field)
            }
        }
    )
}

pub fn is_default(
    autoproto_path: &Path,
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    where_clause_builder: &mut WhereClauseBuilder,
) -> ItemImpl {
    let is_default_where_clause =
        where_clause_builder.with_bound(quote!(#autoproto_path::IsDefault));

    syn::parse_quote!(
        impl #impl_generics #autoproto_path::IsDefault for #ident #ty_generics #is_default_where_clause {
            fn is_default(&self) -> bool {
                #autoproto_path::IsDefault::is_default(&self.#field)
            }
        }
    )
}

pub fn protoscalar<F, T>(
    autoproto_path: &Path,
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
        where_clause_builder.with_bound(quote!(#autoproto_path::ProtoScalar));

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
        impl #impl_generics #autoproto_path::ProtoScalar for #ident #ty_generics #protoscalar_where_clause {
            const DEFAULT_FIXED: #autoproto_path::Fixed = <#field_ty as #autoproto_path::ProtoScalar>::DEFAULT_FIXED;
            const DEFAULT_VARINT: #autoproto_path::Varint = <#field_ty as #autoproto_path::ProtoScalar>::DEFAULT_VARINT;
            const DEFAULT_ENCODING: #autoproto_path::ScalarEncoding = <#field_ty as #autoproto_path::ProtoScalar>::DEFAULT_ENCODING;

            fn from_value(other: #autoproto_path::Value) -> Option<Self> {
                <#field_ty as #autoproto_path::ProtoScalar>::from_value(other)
                    .map(|#field_var| Self #construct)
            }

            fn to_value(&self) -> #autoproto_path::Value {
                #autoproto_path::ProtoScalar::to_value(&self.#field)
            }
        }
    )
}
