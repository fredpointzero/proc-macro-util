// from serde_derive

use super::ctxt::Ctxt;
use proc_macro2::TokenStream;
use quote::ToTokens;

/// A symbol is a string identifier
#[derive(Copy, Clone, Debug)]
pub struct Symbol(pub &'static str);
impl PartialEq<Symbol> for syn::Ident {
    fn eq(&self, word: &Symbol) -> bool {
        self == word.0
    }
}

impl<'a> PartialEq<Symbol> for &'a syn::Ident {
    fn eq(&self, word: &Symbol) -> bool {
        *self == word.0
    }
}

impl PartialEq<Symbol> for syn::Path {
    fn eq(&self, word: &Symbol) -> bool {
        self.is_ident(word.0)
    }
}

impl<'a> PartialEq<Symbol> for &'a syn::Path {
    fn eq(&self, word: &Symbol) -> bool {
        self.is_ident(word.0)
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str(self.0)
    }
}

/// An attribute identified by a symbol
pub struct Attr<'c, T> {
    cx: &'c Ctxt,
    name: Symbol,
    tokens: TokenStream,
    value: Option<T>,
}

impl<'c, T> Attr<'c, T> {
    /// Create an attribute without ay value
    pub fn none(cx: &'c Ctxt, name: Symbol) -> Self {
        Attr {
            cx,
            name,
            tokens: TokenStream::new(),
            value: None,
        }
    }

    /// Set the value of the attribute
    pub fn set<A: ToTokens>(&mut self, obj: A, value: T) {
        let tokens = obj.into_token_stream();

        if self.value.is_some() {
            self.cx.error_spanned_by(
                tokens,
                format!("duplicate composable attribute `{:?}`", self.name),
            );
        } else {
            self.tokens = tokens;
            self.value = Some(value);
        }
    }

    /// Set an optional value of the attribute
    pub fn set_opt<A: ToTokens>(&mut self, obj: A, value: Option<T>) {
        if let Some(value) = value {
            self.set(obj, value);
        }
    }

    /// Set oly if the attribute don't have a value
    pub fn set_if_none(&mut self, value: T) {
        if self.value.is_none() {
            self.value = Some(value);
        }
    }

    /// Get the current value of the attribute
    pub fn get(self) -> Option<T> {
        self.value
    }

    /// Get the value along with the associatd tokens
    pub fn get_with_tokens(self) -> Option<(TokenStream, T)> {
        match self.value {
            Some(v) => Some((self.tokens, v)),
            None => None,
        }
    }
}
