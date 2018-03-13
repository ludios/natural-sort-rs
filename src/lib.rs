//! `natural_sort` is a crate that deals with sorting strings using "natural
//! sorting", (also known as "human sorting").
//!
//! With normal string-based searching, strings are always compared
//! alphabetically:
//!
//! ```
//! let mut files = ["file2.txt", "file11.txt", "file1.txt"];
//! files.sort();
//!
//! // "file11.txt" comes before "file2.txt" because the string "11" comes
//! // before the string "2" in the dictionary.
//! assert_eq!(files, ["file1.txt", "file11.txt", "file2.txt"]);
//! ```
//!
//! This crate provides a function `natural_sort` which will order strings
//! numerically when doing so makes sense:
//!
//! ```
//! use natural_sort::natural_sort;
//!
//! let mut files = ["file1.txt", "file11.txt", "file2.txt"];
//! natural_sort(&mut files);
//!
//! // Here, "file11.txt" comes last because `natural_sort` saw that there was a
//! // number inside the string, and did a numerical, rather than lexical,
//! // comparison.
//! assert_eq!(files, ["file1.txt", "file2.txt", "file11.txt"]);
//! ```
//!
//! Human-comparable strings can be created directly using
//! `natural_sort::HumanStr::new`.

#[macro_use]
extern crate lazy_static;
extern crate num;
extern crate regex;

use num::bigint::BigInt;
use regex::Regex;

use std::cmp::Ordering;
use std::str::FromStr;

lazy_static! {
    static ref NUMBERS: Regex = Regex::new("^[0-9]+").unwrap();
    static ref LETTERS: Regex = Regex::new("^[^0-9]+").unwrap();
}

macro_rules! impl_new {
    ($elem_ty: ty, $struct: ident, $ret_ty: ty) => {
        #[inline]
        /// Constructs a `$struct_ty` from a `$elem_ty`.
        pub fn new(mut rest: $elem_ty) -> $ret_ty {
            let mut elems = Vec::new();
            while !rest.is_empty() {
                let (token, new_rest) = Self::process_token(rest);

                elems.push(token);
                rest = new_rest;
            }
            $struct { elems }
        }
    };
}

macro_rules! impl_process_token {
    ($elem_ty: ty, $inner_elem_ty: ty, $numbers_fun: expr, $letters_fun: expr) => {
        fn process_token(input: $elem_ty) -> ($inner_elem_ty, $elem_ty) {
            if let Some(pos_end) = (*NUMBERS).find(&input).map(|m| m.end()) {
                $numbers_fun(input, pos_end)
            } else {
                let pos_end = (*LETTERS).find(&input).unwrap().end();
                $letters_fun(input, pos_end)
            }
        }
    };
}

macro_rules! impl_partial_ord {
    ($elem_ident:ident, $struct:ident) => {
        #[inline]
        /// `$struct`s are ordered based on their sub-components (a
        /// `$struct` is represented as a sequence of numbers and strings). If
        /// two strings have analogous components, then they can be compared:
        ///
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            // First, create a list of Option<Ordering>s. If there's a type
            // mismatch, have the comparison resolve to `None`.
            let pairs = self.elems.iter().zip(other.elems.iter());
            let compares = pairs.map(|pair| match pair {
                (&$elem_ident::Number(ref a), &$elem_ident::Number(ref b)) => a.partial_cmp(b),
                (&$elem_ident::Letters(ref a), &$elem_ident::Letters(ref b)) => a.partial_cmp(b),
                _ => None,
            });

            // The first time we run into anything that isn't just Some(Ordering::Equal),
            // return it.
            for comparison in compares {
                match comparison {
                    Some(Ordering::Equal) => {}
                    unequal => {
                        return unequal;
                    }
                }
            }

            // If we're still here, then all comparisons resulted in Some(Ordering::Equal). We
            // then fall back to comparing the length of the two strings' elems.
            self.elems.len().partial_cmp(&other.elems.len())
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum StrElem<'a> {
    Letters(&'a str),
    Number(BigInt),
}

/// A `HumanStr` is a sort of string-like object that can be compared in a
/// human-friendly way.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HumanStr<'a> {
    elems: Vec<StrElem<'a>>,
}

impl<'a> HumanStr<'a> {
    impl_new!(&'a str, HumanStr, HumanStr<'a>);
    impl_process_token!(
        &'a str,
        StrElem<'a>,
        |input: &'a str, pos_end| (
            StrElem::Number(BigInt::from_str(&input[..pos_end]).unwrap()),
            &input[pos_end..],
        ),
        |input: &'a str, pos_end| (StrElem::Letters(&input[..pos_end]), &input[pos_end..])
    );
}

/// A utility function for sorting a list of strings using human sorting.
impl<'a> PartialOrd for HumanStr<'a> {
    /// ```
    /// use natural_sort::HumanStr;
    ///
    /// assert!(HumanStr::new("a1a") < HumanStr::new("a1b"));
    /// assert!(HumanStr::new("a11") > HumanStr::new("a2"));
    /// ```
    ///
    /// However, `HumanStr`s cannot always be compared. If the components of
    /// two strings do not match before a difference is found, then no
    /// comparison can be made:
    ///
    /// ```
    /// use natural_sort::HumanStr;
    ///
    /// let a = HumanStr::new("123");
    /// let b = HumanStr::new("abc");
    ///
    /// assert_eq!(a.partial_cmp(&b), None);
    /// ```
    impl_partial_ord!(StrElem, HumanStr);
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum StringElem {
    Letters(String),
    Number(BigInt),
}

/// A `HumanString` is a sort of string-like object that can be compared in a
/// human-friendly way.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HumanString {
    elems: Vec<StringElem>,
}

impl HumanString {
    impl_new!(String, HumanString, HumanString);
    impl_process_token!(
        String,
        StringElem,
        |mut input: String, pos_end| {
            let number = StringElem::Number(BigInt::from_str(&input[..pos_end]).unwrap());
            input.drain(..pos_end).count();
            (number, input)
        },
        |mut input: String, pos_end| {
            let rest = input.split_off(pos_end - 1);
            (StringElem::Letters(input), rest)
        }
    );
}

impl PartialOrd for HumanString {
    /// ```
    /// use natural_sort::HumanString;
    ///
    /// assert!(HumanString::new("a1a") < HumanString::new("a1b"));
    /// assert!(HumanString::new("a11") > HumanString::new("a2"));
    /// ```
    ///
    /// However, `HumanString`s cannot always be compared. If the components of
    /// two strings do not match before a difference is found, then no
    /// comparison can be made:
    ///
    /// ```
    /// use natural_sort::HumanString;
    ///
    /// let a = HumanString::new("123");
    /// let b = HumanString::new("abc");
    ///
    /// assert_eq!(a.partial_cmp(&b), None);
    /// ```
    impl_partial_ord!(StringElem, HumanString);
}

///
/// ```
/// use natural_sort::natural_sort;
///
/// let mut files = ["file1.txt", "file11.txt", "file2.txt"];
/// natural_sort(&mut files);
///
/// assert_eq!(files, ["file1.txt", "file2.txt", "file11.txt"]);
/// ```
pub fn natural_sort(strs: &mut [&str]) {
    fn sort_fn(a: &&str, b: &&str) -> Ordering {
        let seq_a = HumanStr::new(*a);
        let seq_b = HumanStr::new(*b);

        seq_a.partial_cmp(&seq_b).unwrap()
    }

    strs.sort_by(sort_fn);
}

#[cfg(test)]
use num::bigint::ToBigInt;

#[test]
fn test_makes_numseq() {
    let str1 = "123";
    let hstr1 = HumanStr {
        elems: vec![StrElem::Number(123.to_bigint().unwrap())],
    };
    assert_eq!(HumanStr::new(str1), hstr1);

    let str2 = "abc";
    let hstr2 = HumanStr {
        elems: vec![StrElem::Letters("abc")],
    };
    assert_eq!(HumanStr::new(str2), hstr2);

    let str3 = "abc123xyz456";
    let hstr3 = HumanStr {
        elems: vec![
            StrElem::Letters("abc"),
            StrElem::Number(123.to_bigint().unwrap()),
            StrElem::Letters("xyz"),
            StrElem::Number(456.to_bigint().unwrap()),
        ],
    };
    assert_eq!(HumanStr::new(str3), hstr3);
}

#[test]
fn test_compares_numseq() {
    fn compare_numseq(str1: &str, str2: &str) -> Option<Ordering> {
        HumanStr::new(str1).partial_cmp(&HumanStr::new(str2))
    }

    assert_eq!(compare_numseq("aaa", "aaa"), Some(Ordering::Equal));
    assert_eq!(compare_numseq("aaa", "aab"), Some(Ordering::Less));
    assert_eq!(compare_numseq("aab", "aaa"), Some(Ordering::Greater));
    assert_eq!(compare_numseq("aaa", "aa"), Some(Ordering::Greater));

    assert_eq!(compare_numseq("111", "111"), Some(Ordering::Equal));
    assert_eq!(compare_numseq("111", "112"), Some(Ordering::Less));
    assert_eq!(compare_numseq("112", "111"), Some(Ordering::Greater));

    assert_eq!(compare_numseq("a1", "a1"), Some(Ordering::Equal));
    assert_eq!(compare_numseq("a1", "a2"), Some(Ordering::Less));
    assert_eq!(compare_numseq("a2", "a1"), Some(Ordering::Greater));

    assert_eq!(compare_numseq("1a2", "1b1"), Some(Ordering::Less));

    assert_eq!(compare_numseq("1", "a"), None);
}

#[test]
fn test_nonascii_digits() {
    HumanStr::new("٩");
}

#[test]
fn test_natural_sort() {
    let mut files = ["file1.txt", "file11.txt", "file2.txt"];
    natural_sort(&mut files);

    assert_eq!(files, ["file1.txt", "file2.txt", "file11.txt"]);
}
