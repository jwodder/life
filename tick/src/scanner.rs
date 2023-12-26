use std::num::ParseIntError;
use thiserror::Error;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct Scanner<'a>(&'a str);

impl<'a> Scanner<'a> {
    pub(crate) fn new(s: &'a str) -> Scanner<'a> {
        Scanner(s)
    }

    pub(crate) fn skip_whitespace(&mut self) {
        self.0 = self.0.trim_start();
    }

    pub(crate) fn scan_usize(&mut self) -> Result<usize, ScannerError> {
        let Some((digits, s)) = scan_some(self.0, |c| c.is_ascii_digit()) else {
            if let Some(c) = self.peek_char() {
                return Err(ScannerError::NoIntButChar(c));
            } else {
                return Err(ScannerError::NoIntButEof);
            }
        };
        let value = digits.parse::<usize>()?;
        self.0 = s;
        Ok(value)
    }

    pub(crate) fn maybe_scan_usize(&mut self) -> Result<Option<usize>, ScannerError> {
        let Some((digits, s)) = scan_some(self.0, |c| c.is_ascii_digit()) else {
            return Ok(None);
        };
        let value = digits.parse::<usize>()?;
        self.0 = s;
        Ok(Some(value))
    }

    pub(crate) fn scan_char(&mut self, ch: char) -> Result<(), ScannerError> {
        if let Some(t) = self.0.strip_prefix(ch) {
            self.0 = t;
            Ok(())
        } else if let Some(got) = self.peek_char() {
            Err(ScannerError::WrongChar { expected: ch, got })
        } else {
            Err(ScannerError::NotCharButEof(ch))
        }
    }

    pub(crate) fn maybe_scan_char(&mut self, ch: char) -> bool {
        if let Some(t) = self.0.strip_prefix(ch) {
            self.0 = t;
            true
        } else {
            false
        }
    }

    pub(crate) fn peek_char(&self) -> Option<char> {
        self.0.chars().next()
    }

    pub(crate) fn scan_to(&mut self, ch: char) -> Option<&str> {
        let i = self.0.find(ch).unwrap_or(self.0.len());
        (i > 0).then(|| {
            let s = &self.0[..i];
            self.0 = &self.0[i..];
            s
        })
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub(crate) enum ScannerError {
    #[error("expected integer, got {0:?}")]
    NoIntButChar(char),
    #[error("expected integer, got end of string")]
    NoIntButEof,
    #[error("expected {expected:?}, got {got:?}")]
    WrongChar { expected: char, got: char },
    #[error("expected {0:?}, got end of string")]
    NotCharButEof(char),
    #[error("numeric value exceeds integer bounds")]
    NumericOverflow(#[from] ParseIntError),
}

/// Divides a string in two before the first character that does not satisfy
/// the given predicate.  If the first part is nonempty, the parts are
/// returned.  Otherwise, `None` is returned.
///
/// Note that the first part is the maximal leading substring of `s` whose
/// characters all satisfy `predicate`.
fn scan_some<P: FnMut(char) -> bool>(s: &str, mut predicate: P) -> Option<(&str, &str)> {
    let boundary = s
        .char_indices()
        .find(move |&(_, ch)| !predicate(ch))
        .map_or(s.len(), |(i, _)| i);
    (boundary > 0).then(|| s.split_at(boundary))
}
