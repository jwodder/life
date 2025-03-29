use life_utils::{Scanner, ScannerError};
use lifelib::{errors::ParseLineError, utilities::Line};
use std::fmt::Write;
use std::path::MAIN_SEPARATOR;
use std::str::FromStr;
use thiserror::Error;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TickTemplate(Vec<Item>);

impl TickTemplate {
    pub(crate) fn extension(&self) -> Option<&str> {
        let Some(Item::Literal(s)) = self.0.last() else {
            return None;
        };
        match s.rsplit_once('.')? {
            ("", _) if self.0.len() == 1 => None,
            (s, _) if s.ends_with(['/', MAIN_SEPARATOR]) => None,
            (_, ext) => Some(ext),
        }
    }

    pub(crate) fn is_literal(&self) -> bool {
        matches!(self.0.as_slice(), [] | [Item::Literal(_)])
    }

    pub(crate) fn render(&self, value: usize) -> Line {
        let mut s = String::new();
        for item in &self.0 {
            match *item {
                Item::Literal(ref ss) => s.push_str(ss),
                Item::Number {
                    mut flag,
                    width,
                    precision,
                } => {
                    let Ok(digits) =
                        usize::try_from(value.checked_ilog10().unwrap_or_default() + 1)
                    else {
                        unreachable!("The number of digits in a usize should fit in a usize");
                    };
                    let (pre_zeroes, padwidth);
                    if let Some(p) = precision {
                        pre_zeroes = p.saturating_sub(digits);
                        padwidth = width.saturating_sub(digits.max(p));
                        if flag == Flag::Zero {
                            flag = Flag::None;
                        }
                    } else {
                        pre_zeroes = 0;
                        padwidth = width.saturating_sub(digits);
                    }
                    if padwidth > 0 && matches!(flag, Flag::None | Flag::Zero) {
                        let pad = if flag == Flag::Zero { '0' } else { ' ' };
                        for _ in 0..padwidth {
                            s.push(pad);
                        }
                    }
                    for _ in 0..pre_zeroes {
                        s.push('0');
                    }
                    write!(s, "{value}").expect("writing to a String should not fail");
                    if padwidth > 0 && flag == Flag::Left {
                        for _ in 0..padwidth {
                            s.push(' ');
                        }
                    }
                }
            }
        }
        Line::try_from(s).expect("rendered template should not contain newlines")
    }
}

impl FromStr for TickTemplate {
    type Err = TickTemplateError;

    // False positive that is inapplicable due to side effects:
    #[allow(clippy::if_then_some_else_none)]
    fn from_str(s: &str) -> Result<TickTemplate, TickTemplateError> {
        let mut scanner = Scanner::new(s);
        let mut builder = TemplateBuilder::new();
        loop {
            if scanner.maybe_expect_char('%') {
                if scanner.maybe_expect_char('%') {
                    builder.push("%".parse::<Line>().expect(r#""%" should be a valid Line"#));
                } else {
                    let flag = if scanner.maybe_expect_char('0') {
                        Flag::Zero
                    } else if scanner.maybe_expect_char('-') {
                        Flag::Left
                    } else {
                        Flag::None
                    };
                    let width = scanner.maybe_scan_usize()?.unwrap_or_default();
                    let precision = if scanner.maybe_expect_char('.') {
                        Some(scanner.scan_usize()?)
                    } else {
                        None
                    };
                    scanner.expect_char('d')?;
                    builder.number(flag, width, precision);
                }
            } else if let Some(t) = scanner.scan_to('%') {
                builder.push(t.parse::<Line>()?);
            } else {
                debug_assert!(scanner.is_empty(), "scanner should be empty here");
                break;
            }
        }
        Ok(builder.build())
    }
}

#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub(crate) enum TickTemplateError {
    #[error("newline character {:?} not allowed in template", .0.0)]
    Newline(#[from] ParseLineError),

    #[error(transparent)]
    Scanner(#[from] ScannerError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Item {
    Literal(Line),
    Number {
        flag: Flag,
        width: usize,
        precision: Option<usize>,
    },
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Flag {
    Zero,
    Left,
    None,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TemplateBuilder(Vec<Item>);

impl TemplateBuilder {
    fn new() -> TemplateBuilder {
        TemplateBuilder(Vec::new())
    }

    fn push(&mut self, s: Line) {
        if let Some(Item::Literal(ss)) = self.0.last_mut() {
            ss.push_line(&s);
        } else {
            self.0.push(Item::Literal(s));
        }
    }

    fn number(&mut self, flag: Flag, width: usize, precision: Option<usize>) {
        self.0.push(Item::Number {
            flag,
            width,
            precision,
        });
    }

    fn build(self) -> TickTemplate {
        TickTemplate(self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use rstest::rstest;

    #[rstest]
    #[case("", 42, "")]
    #[case("foo", 42, "foo")]
    #[case("%%d", 42, "%d")]
    #[case("[%d]", 42, "[42]")]
    #[case("[%6d]", 42, "[    42]")]
    #[case("[%6.5d]", 42, "[ 00042]")]
    #[case("[%5.6d]", 42, "[000042]")]
    #[case("[%.6d]", 42, "[000042]")]
    #[case("[%0.6d]", 42, "[000042]")]
    #[case("[%06d]", 42, "[000042]")]
    #[case("[%06.5d]", 42, "[ 00042]")]
    #[case("[%06.0d]", 42, "[    42]")]
    #[case("[%-6d]", 42, "[42    ]")]
    #[case("[%-6.5d]", 42, "[00042 ]")]
    #[case("[%6d]", 1234567, "[1234567]")]
    #[case("[%6.5d]", 1234567, "[1234567]")]
    #[case("[%5.6d]", 1234567, "[1234567]")]
    #[case("[%.6d]", 1234567, "[1234567]")]
    #[case("[%0.6d]", 1234567, "[1234567]")]
    #[case("[%06d]", 1234567, "[1234567]")]
    #[case("[%-6d]", 1234567, "[1234567]")]
    fn render(#[case] s: &str, #[case] value: usize, #[case] output: &str) {
        let template = s.parse::<TickTemplate>().unwrap();
        assert_eq!(template.render(value), output);
    }

    #[rstest]
    #[case("foo.ext", Some("ext"))]
    #[case("foo.", Some(""))]
    #[case(".foo", None)]
    #[case("/.foo", None)]
    #[case("bar/.foo", None)]
    #[case(".%doo", None)]
    #[case("bar.%doo", None)]
    #[case("", None)]
    #[case("%d.oo", Some("oo"))]
    #[case("bar/%d.oo", Some("oo"))]
    #[case("bar\\%d.oo", Some("oo"))]
    fn extension(#[case] s: &str, #[case] ext: Option<&str>) {
        let template = s.parse::<TickTemplate>().unwrap();
        assert_eq!(template.extension(), ext);
    }

    #[cfg(windows)]
    #[test]
    fn extension_after_backslash() {
        let template = "bar\\.foo".parse::<TickTemplate>().unwrap();
        assert_eq!(template.extension(), None);
    }

    #[cfg(unix)]
    #[test]
    fn extension_after_backslash() {
        let template = "bar\\.foo".parse::<TickTemplate>().unwrap();
        assert_eq!(template.extension(), Some("foo"));
    }

    #[test]
    fn bad_placeholder() {
        let e = "[%e]".parse::<TickTemplate>().unwrap_err();
        assert_eq!(
            e,
            TickTemplateError::Scanner(ScannerError::WrongChar {
                expected: 'd',
                got: 'e'
            })
        );
        assert_eq!(e.to_string(), "expected 'd', got 'e'");
    }

    #[cfg(any(
        target_pointer_width = "16",
        target_pointer_width = "32",
        target_pointer_width = "64"
    ))]
    #[test]
    fn giant_width() {
        let e = "[%18446744073709551616d]"
            .parse::<TickTemplate>()
            .unwrap_err();
        assert_matches!(
            e,
            TickTemplateError::Scanner(ScannerError::NumericOverflow(_))
        );
        assert_eq!(e.to_string(), "numeric value exceeds integer bounds");
    }

    #[cfg(any(
        target_pointer_width = "16",
        target_pointer_width = "32",
        target_pointer_width = "64"
    ))]
    #[test]
    fn giant_precision() {
        let e = "[%.18446744073709551616d]"
            .parse::<TickTemplate>()
            .unwrap_err();
        assert_matches!(
            e,
            TickTemplateError::Scanner(ScannerError::NumericOverflow(_))
        );
        assert_eq!(e.to_string(), "numeric value exceeds integer bounds");
    }

    #[test]
    fn bad_flag() {
        let e = "[%+d]".parse::<TickTemplate>().unwrap_err();
        assert_eq!(
            e,
            TickTemplateError::Scanner(ScannerError::WrongChar {
                expected: 'd',
                got: '+'
            })
        );
        assert_eq!(e.to_string(), "expected 'd', got '+'");
    }

    #[test]
    fn percent_then_eof() {
        let e = "[%".parse::<TickTemplate>().unwrap_err();
        assert_eq!(
            e,
            TickTemplateError::Scanner(ScannerError::NotCharButEof('d'))
        );
        assert_eq!(e.to_string(), "expected 'd', got end of string");
    }

    #[test]
    fn empty_precision() {
        let e = "[%.d]".parse::<TickTemplate>().unwrap_err();
        assert_eq!(
            e,
            TickTemplateError::Scanner(ScannerError::NoIntButChar('d'))
        );
        assert_eq!(e.to_string(), "expected integer, got 'd'");
    }

    #[test]
    fn period_then_eof() {
        let e = "[%.".parse::<TickTemplate>().unwrap_err();
        assert_eq!(e, TickTemplateError::Scanner(ScannerError::NoIntButEof));
        assert_eq!(e.to_string(), "expected integer, got end of string");
    }

    #[rstest]
    #[case("foo", true)]
    #[case("foo%d", false)]
    #[case("%dfoo", false)]
    #[case("foo%dbar", false)]
    #[case("foo%%", true)]
    #[case("", true)]
    fn is_literal(#[case] s: &str, #[case] b: bool) {
        let template = s.parse::<TickTemplate>().unwrap();
        assert_eq!(template.is_literal(), b);
    }

    #[test]
    fn newline() {
        let e = "foo\n%d.cells".parse::<TickTemplate>().unwrap_err();
        assert_eq!(e, TickTemplateError::Newline(ParseLineError('\n')));
        assert_eq!(
            e.to_string(),
            "newline character '\\n' not allowed in template"
        );
    }
}
