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
//! `natural_sort::HumanString::from_str`.

#[macro_use]
extern crate lazy_static;
extern crate num;
extern crate regex;

use num::bigint::BigInt;
use regex::Regex;

use std::cmp::Ordering;
use std::str::FromStr;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum StringElem<'a> {
    Letters(&'a str),
    Number(BigInt),
}

/// A `HumanString` is a sort of string-like object that can be compared in a
/// human-friendly way.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HumanString<'a> {
    elems: Vec<StringElem<'a>>,
}

impl<'a> HumanString<'a> {
    #[inline]
    /// Constructs a `HumanString` from a `&str`.
    pub fn from_str(mut rest: &'a str) -> HumanString<'a> {
        let mut elems = Vec::new();
        while !rest.is_empty() {
            let (token, new_rest) = HumanString::process_token(rest);

            elems.push(token);
            rest = new_rest;
        }

        HumanString { elems }
    }

    fn process_token(input: &'a str) -> (StringElem<'a>, &str) {
        lazy_static! {
            static ref NUMBERS: Regex = Regex::new("^[0-9]+").unwrap();
            static ref LETTERS: Regex = Regex::new("^[^0-9]+").unwrap();
        }

        if let Some(pos_end) = (*NUMBERS).find(input).map(|m| m.end()) {
            (
                StringElem::Number(BigInt::from_str(&input[..pos_end]).unwrap()),
                &input[pos_end..],
            )
        } else {
            let pos_end = (*LETTERS).find(input).unwrap().end();
            (StringElem::Letters(&input[..pos_end]), &input[pos_end..])
        }
    }
}

/// A utility function for sorting a list of strings using human sorting.
impl<'a> PartialOrd for HumanString<'a> {
    #[inline]
    /// `HumanString`s are ordered based on their sub-components (a
    /// `HumanString` is represented as a sequence of numbers and strings). If
    /// two strings have analogous components, then they can be compared:
    ///
    /// ```
    /// use natural_sort::HumanString;
    ///
    /// assert!(HumanString::from_str("a1a") < HumanString::from_str("a1b"));
    /// assert!(HumanString::from_str("a11") > HumanString::from_str("a2"));
    /// ```
    ///
    /// However, `HumanString`s cannot always be compared. If the components of
    /// two strings do not match before a difference is found, then no
    /// comparison can be made:
    ///
    /// ```
    /// use natural_sort::HumanString;
    ///
    /// let a = HumanString::from_str("123");
    /// let b = HumanString::from_str("abc");
    ///
    /// assert_eq!(a.partial_cmp(&b), None);
    /// ```
    fn partial_cmp(&self, other: &HumanString) -> Option<Ordering> {
        // First, create a list of Option<Ordering>s. If there's a type
        // mismatch, have the comparison resolve to `None`.
        let pairs = self.elems.iter().zip(other.elems.iter());
        let compares = pairs.map(|pair| match pair {
            (&StringElem::Number(ref a), &StringElem::Number(ref b)) => a.partial_cmp(b),
            (&StringElem::Letters(a), &StringElem::Letters(b)) => a.partial_cmp(b),
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
        let seq_a = HumanString::from_str(*a);
        let seq_b = HumanString::from_str(*b);

        seq_a.partial_cmp(&seq_b).unwrap()
    }

    strs.sort_by(sort_fn);
}

#[cfg(test)]
use num::bigint::ToBigInt;

#[test]
fn test_makes_numseq() {
    let str1 = "123";
    let hstr1 = HumanString {
        elems: vec![StringElem::Number(123.to_bigint().unwrap())],
    };
    assert_eq!(HumanString::from_str(str1), hstr1);

    let str2 = "abc";
    let hstr2 = HumanString {
        elems: vec![StringElem::Letters("abc")],
    };
    assert_eq!(HumanString::from_str(str2), hstr2);

    let str3 = "abc123xyz456";
    let hstr3 = HumanString {
        elems: vec![
            StringElem::Letters("abc"),
            StringElem::Number(123.to_bigint().unwrap()),
            StringElem::Letters("xyz"),
            StringElem::Number(456.to_bigint().unwrap()),
        ],
    };
    assert_eq!(HumanString::from_str(str3), hstr3);
}

#[test]
fn test_compares_numseq() {
    fn compare_numseq(str1: &str, str2: &str) -> Option<Ordering> {
        HumanString::from_str(str1).partial_cmp(&HumanString::from_str(str2))
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
    HumanString::from_str("٩");
}

#[test]
fn test_natural_sort() {
    let mut files = ["file1.txt", "file11.txt", "file2.txt"];
    natural_sort(&mut files);

    assert_eq!(files, ["file1.txt", "file2.txt", "file11.txt"]);
}
