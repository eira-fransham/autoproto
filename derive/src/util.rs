use anyhow::{anyhow, bail};
use proc_macro2::TokenStream as TokenStream2;
use quote::ToTokens;
use std::{
    borrow::{Borrow, Cow},
    num::NonZeroU32,
};
use syn::{
    punctuated::Punctuated, Attribute, GenericParam, Generics, Ident, Lit, LitBool, Meta, MetaList,
    NestedMeta, Type, WhereClause, WherePredicate,
};

pub type Result<T> = std::result::Result<T, anyhow::Error>;

pub struct WhereClauseBuilder<Fields = ()> {
    type_params: Vec<Ident>,
    field_types: Fields,
    where_clause: WhereClause,
}

impl<Fields> WhereClauseBuilder<Fields> {
    pub fn with_field_types(generics: &Generics, field_types: Fields) -> Self {
        let WhereClauseBuilder {
            type_params,
            where_clause,
            field_types: (),
        } = WhereClauseBuilder::new(generics);

        WhereClauseBuilder {
            type_params,
            where_clause,
            field_types,
        }
    }
}

impl WhereClauseBuilder {
    pub fn new(generics: &Generics) -> Self {
        let (_, _, where_clause) = generics.split_for_impl();

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
            .map(WhereClause::clone)
            .unwrap_or_else(|| WhereClause {
                where_token: Default::default(),
                predicates: Punctuated::new(),
            });

        Self {
            type_params,
            field_types: (),
            where_clause,
        }
    }
}

impl<Fields> WhereClauseBuilder<Fields> {
    pub fn build(&self) -> AmendedWhereClause<'_, Fields> {
        AmendedWhereClause {
            builder: self,
            where_clause: Cow::Borrowed(&self.where_clause),
        }
    }

    pub fn with_bound<T: ToTokens>(&self, bound: T) -> AmendedWhereClause<'_, Fields> {
        self.build().with_bound(bound)
    }

    pub fn with_self_bound<T: ToTokens>(&self, bound: T) -> AmendedWhereClause<'_, Fields> {
        self.build().with_self_bound(bound)
    }
}

impl<Fields> WhereClauseBuilder<Fields>
where
    Fields: Clone + IntoIterator,
    <Fields as IntoIterator>::Item: Borrow<Type>,
{
    pub fn with_field_bound<T: ToTokens>(&self, bound: T) -> AmendedWhereClause<'_, Fields> {
        self.build().with_field_bound(bound)
    }
}

pub struct AmendedWhereClause<'a, Fields = ()> {
    builder: &'a WhereClauseBuilder<Fields>,
    where_clause: Cow<'a, WhereClause>,
}

impl<Fields> std::ops::Deref for AmendedWhereClause<'_, Fields> {
    type Target = WhereClause;

    fn deref(&self) -> &Self::Target {
        &*self.where_clause
    }
}

impl<Fields> ToTokens for AmendedWhereClause<'_, Fields> {
    fn to_token_stream(&self) -> TokenStream2 {
        self.where_clause.to_token_stream()
    }

    fn into_token_stream(self) -> TokenStream2
    where
        Self: Sized,
    {
        self.where_clause.into_token_stream()
    }

    fn to_tokens(&self, tokens: &mut TokenStream2) {
        self.where_clause.to_tokens(tokens)
    }
}

impl<Fields> AmendedWhereClause<'_, Fields> {
    pub fn with_bound<T: ToTokens>(mut self, bound: T) -> Self {
        let where_clause = self.where_clause.to_mut();

        where_clause.predicates.extend(
            self.builder
                .type_params
                .iter()
                .map::<WherePredicate, _>(|bounded_type| syn::parse_quote!(#bounded_type: #bound)),
        );

        self
    }

    pub fn with_self_bound<T: ToTokens>(mut self, bound: T) -> Self {
        // We trigger the "trivial bounds" lint if we try to add a `Self`
        // bound to a concrete type.
        if !self.builder.type_params.is_empty() {
            self.where_clause
                .to_mut()
                .predicates
                .push(syn::parse_quote!(Self: #bound));
        }

        self
    }
}

impl<Fields> AmendedWhereClause<'_, Fields>
where
    Fields: Clone + IntoIterator,
    <Fields as IntoIterator>::Item: Borrow<Type>,
{
    pub fn with_field_bound<T: ToTokens>(mut self, bound: T) -> Self {
        // We trigger the "trivial bounds" lint if we try to add a `Self`
        // bound to a concrete type.
        if !self.builder.type_params.is_empty() {
            self.where_clause.to_mut().predicates.extend(
                self.builder
                    .field_types
                    .clone()
                    .into_iter()
                    .map::<WherePredicate, _>(|ty| {
                        let ty = ty.borrow();
                        syn::parse_quote!(#ty: #bound)
                    }),
            );
        }

        self
    }
}

#[derive(Debug)]
pub struct FieldAttributes {
    pub tag: Option<NonZeroU32>,
}

impl FieldAttributes {
    pub fn new(attrs: &[Attribute]) -> Result<Self> {
        let mut tag = None::<NonZeroU32>;

        for meta in attrs
            .iter()
            .filter_map(|attr| match attr.parse_meta().ok()? {
                Meta::List(MetaList { nested: inner, .. }) => Some(inner),
                _ => None,
            })
            .flatten()
        {
            if let NestedMeta::Meta(Meta::NameValue(inner)) = meta {
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
        }

        Ok(Self { tag })
    }
}

#[derive(Debug)]
pub struct MessageAttributes {
    pub transparent: bool,
}

impl MessageAttributes {
    pub fn new(attrs: &[Attribute]) -> Result<Self> {
        let mut transparent = false;

        for meta in attrs
            .iter()
            .filter_map(|attr| match attr.parse_meta().ok()? {
                Meta::List(MetaList { nested: inner, .. }) => Some(inner),
                _ => None,
            })
            .flatten()
        {
            if let NestedMeta::Meta(meta) = meta {
                let (ident, value) = match &meta {
                    Meta::Path(inner) => {
                        if let Some(ident) = inner.get_ident() {
                            (ident, true)
                        } else {
                            continue;
                        }
                    }
                    Meta::NameValue(inner) => {
                        if let (Some(ident), Lit::Bool(LitBool { value, .. })) =
                            (inner.path.get_ident(), &inner.lit)
                        {
                            (ident, *value)
                        } else {
                            continue;
                        }
                    }
                    _ => continue,
                };

                if ident == "transparent" {
                    transparent = value;
                }
            }
        }

        Ok(Self { transparent })
    }
}
