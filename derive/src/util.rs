use anyhow::{anyhow, bail};
use proc_macro2::TokenStream as TokenStream2;
use quote::ToTokens;
use std::{borrow::Cow, num::NonZeroU32};
use syn::{
    punctuated::Punctuated, Attribute, GenericParam, Generics, Ident, Lit, LitBool, Meta, MetaList,
    NestedMeta, WhereClause, WherePredicate,
};

pub type Result<T> = std::result::Result<T, anyhow::Error>;

pub struct WhereClauseBuilder {
    type_params: Vec<Ident>,
    where_clause: WhereClause,
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
            where_clause,
        }
    }

    pub fn build(&self) -> AmendedWhereClause<'_> {
        AmendedWhereClause {
            type_params: &self.type_params,
            where_clause: Cow::Borrowed(&self.where_clause),
        }
    }

    pub fn with_bound<T: ToTokens>(&self, bound: T) -> AmendedWhereClause<'_> {
        self.build().with_bound(bound)
    }

    pub fn with_self_bound<T: ToTokens>(&self, bound: T) -> AmendedWhereClause<'_> {
        self.build().with_self_bound(bound)
    }
}

pub struct AmendedWhereClause<'a> {
    type_params: &'a [Ident],
    where_clause: Cow<'a, WhereClause>,
}

impl std::ops::Deref for AmendedWhereClause<'_> {
    type Target = WhereClause;

    fn deref(&self) -> &Self::Target {
        &*self.where_clause
    }
}

impl ToTokens for AmendedWhereClause<'_> {
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

impl AmendedWhereClause<'_> {
    pub fn with_bound<T: ToTokens>(mut self, bound: T) -> Self {
        let where_clause = self.where_clause.to_mut();

        where_clause.predicates.extend(
            self.type_params
                .iter()
                .map::<WherePredicate, _>(|bounded_type| syn::parse_quote!(#bounded_type: #bound)),
        );

        self
    }

    pub fn with_self_bound<T: ToTokens>(mut self, bound: T) -> Self {
        let where_clause = self.where_clause.to_mut();

        // We trigger the "trivial bounds" lint if we try to add a `Self`
        // bound to a concrete type.
        if !self.type_params.is_empty() {
            where_clause
                .predicates
                .push(syn::parse_quote!(Self: #bound));
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
