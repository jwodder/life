use crate::scanner::{Scanner, ScannerError};
use rangemap::RangeInclusiveSet;
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
        let mut scanner = Scanner::new(s);
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
            if scanner.maybe_scan_char('-') {
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

#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub(crate) enum ParseTickSetError {
    #[error("empty tick set not allowed")]
    Empty,
    #[error("decreasing range {start}-{end} not allowed")]
    Decreasing { start: usize, end: usize },
    #[error(transparent)]
    Scanner(#[from] ScannerError),
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
            ParseTickSetError::Scanner(ScannerError::WrongChar {
                expected: ',',
                got: '2'
            })
        );
        assert_eq!(e.to_string(), "expected ',', got '2'");
    }

    #[test]
    fn int_hyphen_eof() {
        let e = "1-".parse::<TickSet>().unwrap_err();
        assert_eq!(e, ParseTickSetError::Scanner(ScannerError::NoIntButEof));
        assert_eq!(e.to_string(), "expected integer, got end of string");
    }

    #[test]
    fn int_hyphen_space_eof() {
        let e = "1- ".parse::<TickSet>().unwrap_err();
        assert_eq!(e, ParseTickSetError::Scanner(ScannerError::NoIntButEof));
        assert_eq!(e.to_string(), "expected integer, got end of string");
    }

    #[test]
    fn int_hyphen_splat() {
        let e = "1-*".parse::<TickSet>().unwrap_err();
        assert_eq!(
            e,
            ParseTickSetError::Scanner(ScannerError::NoIntButChar('*'))
        );
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
        assert_matches!(
            e,
            ParseTickSetError::Scanner(ScannerError::NumericOverflow(_))
        );
        assert_eq!(e.to_string(), "numeric value exceeds integer bounds");
    }
}
