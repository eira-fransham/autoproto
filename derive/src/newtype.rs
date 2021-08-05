use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{Ident, ItemImpl, Member, WhereClause};

pub fn protoencode<F>(
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    make_where_clause: F,
) -> ItemImpl
where
    F: Fn(TokenStream2) -> WhereClause,
{
    let protoencode_where_clause = make_where_clause(quote!(::autoproto::ProtoEncode));

    syn::parse_quote!(
        impl #impl_generics ::autoproto::ProtoEncode for #ident #ty_generics #protoencode_where_clause {
            fn encode_as_field(&self, tag: ::core::num::NonZeroU32, buf: &mut dyn prost::bytes::BufMut) {
                ::autoproto::ProtoEncode::encode_as_field(&self.#field, tag, buf)
            }

            fn encoded_len_as_field(&self, tag: ::core::num::NonZeroU32) -> usize {
                ::autoproto::ProtoEncode::encoded_len_as_field(&self.#field, tag)
            }
        }
    )
}

pub fn proto<F>(
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    make_where_clause: F,
) -> ItemImpl
where
    F: Fn(TokenStream2) -> WhereClause,
{
    let proto_where_clause = make_where_clause(quote!(::autoproto::Proto));

    syn::parse_quote!(
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
    )
}

pub fn message<F>(
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    make_where_clause: F,
) -> ItemImpl
where
    F: Fn(TokenStream2) -> WhereClause,
{
    let message_where_clause = make_where_clause(quote!(::autoproto::prost::Message));

    syn::parse_quote!(
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
    )
}

pub fn is_default<F>(
    ident: &Ident,
    field: &Member,
    impl_generics: &syn::ImplGenerics,
    ty_generics: &syn::TypeGenerics,
    make_where_clause: F,
) -> ItemImpl
where
    F: Fn(TokenStream2) -> WhereClause,
{
    let is_default_where_clause = make_where_clause(quote!(::autoproto::IsDefault));

    syn::parse_quote!(
        impl #impl_generics ::autoproto::IsDefault for #ident #ty_generics #is_default_where_clause {
            fn is_default(&self) -> bool {
                ::autoproto::IsDefault::is_default(&self.#field)
            }
        }
    )
}
