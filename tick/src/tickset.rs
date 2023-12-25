use rangemap::RangeInclusiveSet;
use std::num::ParseIntError;
use std::str::FromStr;
use thiserror::Error;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TickSet(RangeInclusiveSet<usize>);

impl TickSet {
    pub(crate) fn maxvalue(&self) -> usize {
        *self
            .0
            .iter()
            .last()
            .expect("TickSet should be nonempty")
            .end()
    }

    pub(crate) fn contains(&self, value: usize) -> bool {
        self.0.contains(&value)
    }
}

impl FromStr for TickSet {
    type Err = ParseTickSetError;

    fn from_str(s: &str) -> Result<TickSet, ParseTickSetError> {
        let mut scanner = Scanner(s);
        let mut first = true;
        let mut ranges = RangeInclusiveSet::new();
        loop {
            scanner.skip_whitespace();
            if scanner.is_empty() {
                break;
            }
            if !std::mem::replace(&mut first, false) {
                scanner.scan_char(',')?;
                scanner.skip_whitespace();
            }
            let start = scanner.scan_usize()?;
            scanner.skip_whitespace();
            if scanner.peek_char() == Some('-') {
                scanner.scan_char('-')?;
                scanner.skip_whitespace();
                let end = scanner.scan_usize()?;
                if start > end {
                    return Err(ParseTickSetError::Decreasing { start, end });
                }
                ranges.insert(start..=end);
            } else {
                ranges.insert(start..=start);
            }
        }
        if first {
            debug_assert_eq!(ranges.iter().next(), None, "if first, then ranges is empty");
            Err(ParseTickSetError::Empty)
        } else {
            Ok(TickSet(ranges))
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct Scanner<'a>(&'a str);

impl Scanner<'_> {
    fn skip_whitespace(&mut self) {
        self.0 = self.0.trim_start();
    }

    fn scan_usize(&mut self) -> Result<usize, ParseTickSetError> {
        let Some((digits, s)) = scan_some(self.0, |c| c.is_ascii_digit()) else {
            if let Some(c) = self.peek_char() {
                return Err(ParseTickSetError::NoIntButChar(c));
            } else {
                return Err(ParseTickSetError::NoIntButEof);
            }
        };
        let value = digits.parse::<usize>()?;
        self.0 = s;
        Ok(value)
    }

    fn scan_char(&mut self, ch: char) -> Result<(), ParseTickSetError> {
        if let Some(t) = self.0.strip_prefix(ch) {
            self.0 = t;
            Ok(())
        } else if let Some(got) = self.peek_char() {
            Err(ParseTickSetError::WrongChar { expected: ch, got })
        } else {
            Err(ParseTickSetError::NotCharButEof(ch))
        }
    }

    fn peek_char(&self) -> Option<char> {
        self.0.chars().next()
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
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

#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub(crate) enum ParseTickSetError {
    #[error("empty tick set not allowed")]
    Empty,
    #[error("decreasing range {start}-{end} not allowed")]
    Decreasing { start: usize, end: usize },
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

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use rstest::rstest;
    use std::ops::RangeInclusive;

    #[rstest]
    #[case("1", [1..=1].as_slice())]
    #[case(" 1 ", [1..=1].as_slice())]
    #[case("1-1", [1..=1].as_slice())]
    #[case("1-5", [1..=5].as_slice())]
    #[case("1,5", [1..=1, 5..=5].as_slice())]
    #[case("1-2,5", [1..=2, 5..=5].as_slice())]
    #[case("1-3,5", [1..=3, 5..=5].as_slice())]
    #[case("1,4-5", [1..=1, 4..=5].as_slice())]
    #[case("1,3-5", [1..=1, 3..=5].as_slice())]
    #[case(" 1 , 3 - 5 ", [1..=1, 3..=5].as_slice())]
    #[case("3-5, 1", [1..=1, 3..=5].as_slice())]
    #[case("1-2,3-5", [1..=5].as_slice())]
    #[case("1-2,5-7", [1..=2, 5..=7].as_slice())]
    fn parse_tickset(#[case] s: &str, #[case] ranges: &[RangeInclusive<usize>]) {
        let TickSet(rangeset) = s.parse::<TickSet>().unwrap();
        assert_eq!(rangeset.iter().cloned().collect::<Vec<_>>(), ranges);
    }

    #[test]
    fn empty() {
        let e = "".parse::<TickSet>().unwrap_err();
        assert_eq!(e, ParseTickSetError::Empty);
        assert_eq!(e.to_string(), "empty tick set not allowed");
    }

    #[test]
    fn all_whitespace() {
        let e = "  ".parse::<TickSet>().unwrap_err();
        assert_eq!(e, ParseTickSetError::Empty);
        assert_eq!(e.to_string(), "empty tick set not allowed");
    }

    #[test]
    fn decreasing() {
        let e = "5 - 2".parse::<TickSet>().unwrap_err();
        assert_eq!(e, ParseTickSetError::Decreasing { start: 5, end: 2 });
        assert_eq!(e.to_string(), "decreasing range 5-2 not allowed");
    }

    #[test]
    fn good_and_decreasing() {
        let e = "1, 5 - 2".parse::<TickSet>().unwrap_err();
        assert_eq!(e, ParseTickSetError::Decreasing { start: 5, end: 2 });
        assert_eq!(e.to_string(), "decreasing range 5-2 not allowed");
    }

    #[test]
    fn no_comma() {
        let e = "1 2".parse::<TickSet>().unwrap_err();
        assert_eq!(
            e,
            ParseTickSetError::WrongChar {
                expected: ',',
                got: '2'
            }
        );
        assert_eq!(e.to_string(), "expected ',', got '2'");
    }

    #[test]
    fn int_hyphen_eof() {
        let e = "1-".parse::<TickSet>().unwrap_err();
        assert_eq!(e, ParseTickSetError::NoIntButEof);
        assert_eq!(e.to_string(), "expected integer, got end of string");
    }

    #[test]
    fn int_hyphen_space_eof() {
        let e = "1- ".parse::<TickSet>().unwrap_err();
        assert_eq!(e, ParseTickSetError::NoIntButEof);
        assert_eq!(e.to_string(), "expected integer, got end of string");
    }

    #[test]
    fn int_hyphen_splat() {
        let e = "1-*".parse::<TickSet>().unwrap_err();
        assert_eq!(e, ParseTickSetError::NoIntButChar('*'));
        assert_eq!(e.to_string(), "expected integer, got '*'");
    }

    #[cfg(any(
        target_pointer_width = "16",
        target_pointer_width = "32",
        target_pointer_width = "64"
    ))]
    #[test]
    fn giant_value() {
        let e = "18446744073709551616".parse::<TickSet>().unwrap_err();
        assert_matches!(e, ParseTickSetError::NumericOverflow(_));
        assert_eq!(e.to_string(), "numeric value exceeds integer bounds");
    }
}
