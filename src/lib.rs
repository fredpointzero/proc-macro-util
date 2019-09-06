//! Utilities to implement procedural macros

#[cfg(test)]
#[cfg_attr(test, macro_use)]
extern crate quote;

use proc_macro2::{Delimiter, Span, TokenTree};
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

mod attr;
mod ctxt;

pub mod prelude {
    pub use super::attr::*;
    pub use super::ctxt::*;
}

/// An error that is located by a span
#[derive(Debug)]
pub struct SpanError {
    /// The source error
    pub error: failure::Error,
    /// The location of the error
    pub span: Span,
}

impl SpanError {
    /// Build a new `SpanError`
    pub fn from_error(error: failure::Error, span: Span) -> Self {
        Self { error, span }
    }
}

/// Parse keyed arrays of identifiers.
///
/// It expects as an input a parenthesis group, and in this group
/// if it ran into a key in `allowed_key_values`, then it will
/// parse the following tokens as an array of identifiers.
///
/// The values must be in the provided value set.
///
/// # Arguments
/// * `input`: token iterator to consume
/// * `default_span`: A span that will be used if there is an error that can't be
///    linked to a specific span.
/// * `allowed_key_values`: An hash map to define the allowed keys and their corresponding allowed
///    values.
///
/// # Return
/// An hash map with the values found for each keys.
///
/// # Error
/// * When a key is detected but its value is not a bracket group with identifiers separated by commas
/// * When an identifier is not in the allowed identifier list for a specific key
///
/// # Example
///
/// * `(not_array, array_key = [value_1, value_2])`
///    Here `array_key` is defined as a valid key and its
///    following tokens will be processed as an array of identifiers.
///    This will be valid only if both `value_1` and `value_2` are valid identifiers.
pub fn parse_identifier_arrays(
    input: impl IntoIterator<Item = TokenTree>,
    default_span: Span,
    allowed_key_values: &HashMap<&str, &[&str]>,
) -> Result<HashMap<String, Vec<String>>, SpanError> {
    let mut result = HashMap::new();
    let iter = input.into_iter();

    let mut iter = private::consume_group_parenthesis_token(iter, default_span.clone())?;

    loop {
        match iter.next() {
            Some(TokenTree::Ident(ident)) => {
                let ident_str = ident.to_string();
                if allowed_key_values.contains_key(std::ops::Deref::deref(&ident_str)) {
                    private::consume_punct(&mut iter, default_span.clone(), '=')?;

                    // We expect now an array of identifier
                    let values = parse_identifier_array(
                        &mut iter,
                        default_span,
                        &allowed_key_values[std::ops::Deref::deref(&ident_str)],
                    )?;
                    match result.entry(ident_str) {
                        Entry::Vacant(entry) => {
                            entry.insert(values);
                        }
                        Entry::Occupied(mut entry) => {
                            entry.get_mut().extend(values);
                        }
                    }
                }
            }
            None => break,
            _ => {}
        }
    }

    Ok(result)
}

/// Parse an array of identifiers.
///
/// It expects an array of predefined identifiers.
///
/// # Arguments
/// * `iter`: token iterator to consume
/// * `default_span`: span to use when an error was found but can't be linked to a span.
/// * `allowed_values`: identifiers allowed as values for this array
///
/// # Return
/// The identifiers found for this array.
///
/// # Error
/// * When the tokens is not a bracket group with identifiers separated by commas
/// * When an identifier is not in the allowed identifier list
pub fn parse_identifier_array<I>(
    iter: &mut I,
    default_span: proc_macro2::Span,
    allowed_values: &[&str],
) -> Result<Vec<String>, SpanError>
where
    I: Iterator<Item = TokenTree>,
{
    match iter.next() {
        Some(TokenTree::Group(ref group)) if group.delimiter() == Delimiter::Bracket => {
            let mut group_iter = group.stream().into_iter();
            let mut result = Vec::new();

            loop {
                match group_iter.next() {
                    Some(TokenTree::Ident(ident)) => {
                        let ident_str = ident.to_string();
                        if allowed_values.contains(&std::ops::Deref::deref(&ident_str)) {
                            result.push(ident_str);
                        } else {
                            return Err(SpanError::from_error(
                                failure::err_msg(format!(
                                    "Unexpected value: {:?}, values expected are: {:?}",
                                    ident_str, allowed_values
                                )),
                                ident.span(),
                            ));
                        }

                        match group_iter.next() {
                            Some(TokenTree::Punct(ref punct)) if punct.as_char() == ',' => {}
                            Some(v) => {
                                return Err(SpanError::from_error(
                                    failure::err_msg(format!(
                                        "Unexpected token: {:?}, only ',' is expected",
                                        v.to_string()
                                    )),
                                    private::token_tree_span(&v),
                                ))
                            }
                            None => {}
                        }
                    }
                    Some(v) => {
                        return Err(SpanError::from_error(
                            failure::err_msg(format!(
                                "Unexpected token: {:?}, only a value in {:?} is expected",
                                v.to_string(),
                                allowed_values
                            )),
                            private::token_tree_span(&v),
                        ))
                    }
                    None => break,
                }
            }

            Ok(result)
        }
        Some(v) => {
            return Err(SpanError::from_error(
                failure::err_msg(format!(
                    "Expected an array of values, but received: {}",
                    v.to_string()
                )),
                private::token_tree_span(&v),
            ))
        }
        None => Err(SpanError::from_error(
            failure::err_msg("Expected an array of values."),
            default_span,
        )),
    }
}

/// Parse tokens as flags toggles
///
/// This will search in the provided token iterator `input` for specific
/// identifier that will toggle on a flag.
///
/// # Arguments
/// * `input`: token iterator to consume
/// * `default_span`: span to use when an error occurs and can't be linked to a span
/// * `allowed_flags`: identifiers that are parsed as flags
///
/// # Return
/// An hash set of toggled flags.
///
/// # Errors
/// if a flag is found but is not parsed as a flag. (Usually followed by a `=` token,
/// which is invalid for a flag)
pub fn parse_flags(
    input: impl IntoIterator<Item = TokenTree>,
    default_span: proc_macro2::Span,
    allowed_flags: &[&str],
) -> Result<HashSet<String>, SpanError> {
    let mut result = HashSet::new();
    let iter = input.into_iter();

    let mut iter = private::consume_group_parenthesis_token(iter, default_span.clone())?;

    loop {
        match iter.next() {
            Some(TokenTree::Ident(ident)) => {
                let ident_str = ident.to_string();
                if allowed_flags.contains(&std::ops::Deref::deref(&ident_str)) {
                    // Check that following token is either , or EOF
                    match iter.next() {
                        Some(TokenTree::Punct(ref punct)) if punct.as_char() == ',' => {},
                        None => {},
                        Some(v) => {
                            return Err(SpanError::from_error(
                                failure::err_msg(format!(
                                    "'{}' must be used as a flag, it must be followed by a ',' or another argument.", ident_str
                                )),
                                private::token_tree_span(&v)
                            ))
                        }
                    }

                    result.insert(ident.to_string());
                }
            }
            None => break,
            _ => {}
        }
    }

    Ok(result)
}

/// Parse strings identified by keys
///
/// # Argument
/// * `input`: token iterator to consume
/// * `default_span`: span to use when an error is detected but can't be linked to a span
/// * `keys`: keys to search for
///
/// # Return
/// An hash map with the key that were detected with their associated value.
/// The value contains the quote that makes the string literal.
///
/// # Error
/// * When a key was detected but can't be parsed as a string literal assignment
///
/// # Example
/// `(my_val = "toto"), then the value of identifier `my_val` is `r#""toto""#`.
pub fn parse_keyed_strings(
    input: impl IntoIterator<Item = TokenTree>,
    default_span: proc_macro2::Span,
    keys: &[&str],
) -> Result<HashMap<String, String>, SpanError> {
    let mut result = HashMap::new();
    let iter = input.into_iter();

    let mut iter = private::consume_group_parenthesis_token(iter, default_span.clone())?;

    loop {
        match iter.next() {
            Some(TokenTree::Ident(ident)) => {
                let ident_str = ident.to_string();
                if keys.contains(&std::ops::Deref::deref(&ident_str)) {
                    // Extract value as a string

                    // Extract '=' token
                    match iter.next() {
                        Some(TokenTree::Punct(ref punct)) if punct.as_char() == '=' => {}
                        Some(v) => {
                            return Err(SpanError::from_error(
                                failure::err_msg(format!(
                                    "Expected a string value for {:?}, but received: {:?}",
                                    ident_str,
                                    v.to_string()
                                )),
                                private::token_tree_span(&v),
                            ))
                        }
                        _ => {
                            return Err(SpanError::from_error(
                                failure::err_msg(format!(
                                    "Expected a string value for {:?}, but received none",
                                    ident_str
                                )),
                                default_span,
                            ))
                        }
                    };

                    // Extract value
                    match iter.next() {
                        Some(TokenTree::Literal(ref literal)) => {
                            let old = result.insert(ident_str.clone(), literal.to_string());
                            if old.is_some() {
                                return Err(SpanError::from_error(
                                    failure::err_msg(format!(
                                        "{:?} can appear only once",
                                        ident_str
                                    )),
                                    literal.span(),
                                ));
                            }
                        }
                        Some(v) => {
                            return Err(SpanError::from_error(
                                failure::err_msg(format!(
                                    "Expected a string value for {:?}, but received: {:?}",
                                    ident_str,
                                    v.to_string()
                                )),
                                private::token_tree_span(&v),
                            ))
                        }
                        _ => {
                            return Err(SpanError::from_error(
                                failure::err_msg(format!(
                                    "Expected a string value for {:?}, but received none",
                                    ident_str
                                )),
                                default_span,
                            ))
                        }
                    };
                }
            }
            None => break,
            _ => {}
        }
    }

    Ok(result)
}

mod private {
    use super::SpanError;
    use proc_macro2::{Delimiter, Span, TokenTree};

    pub fn token_tree_span(tree: &TokenTree) -> Span {
        match tree {
            TokenTree::Punct(punct) => punct.span(),
            TokenTree::Ident(ident) => ident.span(),
            TokenTree::Group(group) => group.span(),
            TokenTree::Literal(literal) => literal.span(),
        }
    }

    pub fn consume_punct<I: Iterator<Item = TokenTree>>(
        iter: &mut I,
        default_span: Span,
        value: char,
    ) -> Result<(), SpanError> {
        match iter.next() {
            Some(TokenTree::Punct(ref punct)) if punct.as_char() == value => {}
            Some(v) => {
                return Err(SpanError::from_error(
                    failure::err_msg(format!(
                        "Expected token '{:?}', but received {:?}",
                        value,
                        v.to_string()
                    )),
                    token_tree_span(&v),
                ))
            }
            _ => {
                return Err(SpanError::from_error(
                    failure::err_msg(format!("Expected token '{:?}', but received none", value)),
                    default_span,
                ))
            }
        };
        Ok(())
    }

    pub fn consume_group_parenthesis_token(
        mut iter: impl Iterator<Item = TokenTree>,
        default_span: Span,
    ) -> Result<impl Iterator<Item = TokenTree>, SpanError> {
        match iter.next() {
            Some(TokenTree::Group(ref group)) if group.delimiter() == Delimiter::Parenthesis => {
                Ok(group.stream().into_iter())
            }
            Some(v) => Err(SpanError::from_error(
                failure::err_msg(format!(
                    "Expected a parenthesis group, but received: {:?}",
                    v.to_string()
                )),
                token_tree_span(&v),
            )),
            _ => Err(SpanError::from_error(
                failure::err_msg("Expected a parenthesis group, but received none"),
                default_span,
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{parse_flags, parse_identifier_arrays, parse_keyed_strings};
    use proc_macro2::TokenStream;
    use std::collections::{HashMap, HashSet};
    use syn::spanned::Spanned;
    use syn::DeriveInput;

    #[test]
    fn parse_flag_fails_with_invalid_entry() {
        let input: TokenStream = quote! {
            #[my_attr(my_flag = 3)]
            struct MyAttr;
        };
        let derive_input: DeriveInput = syn::parse2(input).unwrap();
        let attr = &derive_input.attrs[0];

        let flags = parse_flags(attr.tokens.clone().into_iter(), attr.span(), &["my_flag"]);

        assert!(flags.is_err());
    }

    #[test]
    fn parse_flag_works_with_one_entry() {
        let input: TokenStream = quote! {
            #[my_attr(my_flag)]
            struct MyAttr;
        };
        let derive_input: DeriveInput = syn::parse2(input).unwrap();
        let attr = &derive_input.attrs[0];

        let flags =
            parse_flags(attr.tokens.clone().into_iter(), attr.span(), &["my_flag"]).unwrap();

        let expected_flags = vec!["my_flag".to_owned()]
            .into_iter()
            .collect::<HashSet<_>>();

        assert_eq!(flags, expected_flags);
    }

    #[test]
    fn parse_flag_works_with_multiple_entries() {
        let input: TokenStream = quote! {
            #[my_attr(my_flag, my_second_flag)]
            struct MyAttr;
        };
        let derive_input: DeriveInput = syn::parse2(input).unwrap();
        let attr = &derive_input.attrs[0];

        let flags = parse_flags(
            attr.tokens.clone().into_iter(),
            attr.span(),
            &["my_flag", "my_second_flag", "my_third_flag"],
        )
        .unwrap();

        let expected_flags = vec!["my_flag".to_owned(), "my_second_flag".to_owned()]
            .into_iter()
            .collect::<HashSet<_>>();

        assert_eq!(flags, expected_flags);
    }

    #[test]
    fn parse_identifier_arrays_works() {
        let input: TokenStream = quote! {
            #[my_attr(array_key = [entry, entry2])]
            struct MyAttr;
        };
        let derive_input: DeriveInput = syn::parse2(input).unwrap();
        let attr = &derive_input.attrs[0];

        let allowed_keys = vec![("array_key", &["entry", "entry2", "entry3"] as &[&str])]
            .into_iter()
            .collect::<HashMap<_, _>>();

        let values =
            parse_identifier_arrays(attr.tokens.clone().into_iter(), attr.span(), &allowed_keys)
                .unwrap();

        assert!(values.contains_key("array_key"));
        let array_key_values = &values["array_key"].iter().cloned().collect::<HashSet<_>>();
        let expected_array_key_values = vec!["entry".to_owned(), "entry2".to_owned()]
            .into_iter()
            .collect::<HashSet<_>>();
        assert_eq!(array_key_values, &expected_array_key_values);
    }

    #[test]
    fn parse_identifier_arrays_fails_with_invalid_key_entry() {
        let input: TokenStream = quote! {
            #[my_attr(array_key = 3)]
            struct MyAttr;
        };
        let derive_input: DeriveInput = syn::parse2(input).unwrap();
        let attr = &derive_input.attrs[0];

        let allowed_keys = vec![("array_key", &["entry", "entry2", "entry3"] as &[&str])]
            .into_iter()
            .collect::<HashMap<_, _>>();

        let values =
            parse_identifier_arrays(attr.tokens.clone().into_iter(), attr.span(), &allowed_keys);

        assert!(values.is_err());
    }

    #[test]
    fn parse_identifier_arrays_fails_with_invalid_value_entry() {
        let input: TokenStream = quote! {
            #[my_attr(array_key = [entry, entry4])]
            struct MyAttr;
        };
        let derive_input: DeriveInput = syn::parse2(input).unwrap();
        let attr = &derive_input.attrs[0];

        let allowed_keys = vec![("array_key", &["entry", "entry2", "entry3"] as &[&str])]
            .into_iter()
            .collect::<HashMap<_, _>>();

        let values =
            parse_identifier_arrays(attr.tokens.clone().into_iter(), attr.span(), &allowed_keys);

        assert!(values.is_err());
    }

    #[test]
    fn parse_keyed_strings_works() {
        let input: TokenStream = quote! {
            #[my_attr(string_key = "my_value")]
            struct MyAttr;
        };
        let derive_input: DeriveInput = syn::parse2(input).unwrap();
        let attr = &derive_input.attrs[0];

        let values = parse_keyed_strings(
            attr.tokens.clone().into_iter(),
            attr.span(),
            &["string_key"],
        )
        .unwrap();

        assert_eq!(&values["string_key"], &r#""my_value""#);
    }

    #[test]
    fn parse_keyed_strings_fails_with_invalid_entry() {
        let input: TokenStream = quote! {
            #[my_attr(string_key)]
            struct MyAttr;
        };
        let derive_input: DeriveInput = syn::parse2(input).unwrap();
        let attr = &derive_input.attrs[0];

        let values = parse_keyed_strings(
            attr.tokens.clone().into_iter(),
            attr.span(),
            &["string_key"],
        );

        assert!(values.is_err());
    }

    #[test]
    fn parse_keyed_strings_fails_with_invalid_entry2() {
        let input: TokenStream = quote! {
            #[my_attr(string_key = [43])]
            struct MyAttr;
        };
        let derive_input: DeriveInput = syn::parse2(input).unwrap();
        let attr = &derive_input.attrs[0];

        let values = parse_keyed_strings(
            attr.tokens.clone().into_iter(),
            attr.span(),
            &["string_key"],
        );

        assert!(values.is_err());
    }
}
