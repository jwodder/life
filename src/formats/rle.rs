use super::util::{ascii_lines, scan_some, split_at_newline};
use crate::{Edges, Pattern};
use std::fmt;
use std::iter::FusedIterator;
use std::num::ParseIntError;
use std::str::FromStr;
use thiserror::Error;

// # Implementation-Specific Parsing Details
//
// - Specifications of cells outside the given width & height are accepted
//   but ignored.
//
// - A '#' line must consist of, in order, a '#', any single non-newline
//   character, one or more space (U+0020) characters (discarded when parsing),
//   and freeform text.
//
// - Tokens in the header line may be separated by zero or more Unicode
//   whitespace characters.
//
// - Tokens in the pattern data may be separated by zero or more Unicode
//   whitespace characters.
//
// - 'b' and 'B' are parsed as dead cells.  All other ASCII letters are parsed
//   as live cells.

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rle {
    pub comments: Vec<(char, String)>,
    pub pattern: Pattern,
}

impl fmt::Display for Rle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (code, text) in &self.comments {
            for ln in ascii_lines(text) {
                writeln!(f, "#{code} {ln}")?;
            }
        }
        writeln!(
            f,
            "x = {}, y = {}",
            self.pattern.width(),
            self.pattern.height()
        )?;
        let mut linelen = 0;
        for item in self.pattern.runs() {
            let len = item.display_len();
            if linelen + len > 70 {
                writeln!(f)?;
                linelen = 0;
            }
            write!(f, "{item}")?;
            linelen += len;
        }
        if linelen + 1 > 70 {
            writeln!(f)?;
        }
        writeln!(f, "!")?;
        Ok(())
    }
}

impl FromStr for Rle {
    type Err = RleError;

    fn from_str(s: &str) -> Result<Rle, RleError> {
        let mut cparser = CommentParser(s);
        let mut comments = Vec::new();
        while let Some((code, text)) = cparser.next_comment()? {
            comments.push((code, text.to_owned()));
        }
        let s = cparser.into_inner();
        let (header, data) = match split_at_newline(s) {
            Some(hd) => hd,
            None if !s.is_empty() => (s, ""),
            _ => return Err(RleError::NoData),
        };
        let (width, height) = parse_header(header)?;
        let mut pattern = Pattern::new(height, width, Edges::default());
        let mut y = 0;
        let mut x = 0;
        for run in parse_runs(data) {
            let (count, tag) = run?;
            match tag {
                Tag::Dead => x += count,
                Tag::Live => pattern.set_live_run(y, x, count),
                Tag::Eol => {
                    y += count;
                    x = 0;
                }
            }
        }
        Ok(Rle { comments, pattern })
    }
}

#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum RleError {
    #[error("'#' line lacks code character")]
    NoCode,
    #[error("no space after {0:?} code in '#' line")]
    NoSpaceAfterCode(char),
    #[error("no data in RLE input")]
    NoData,
    #[error("invalid header line")]
    InvalidHeader,
    #[error("header specifies unsupported rule")]
    UnsupportedRule,
    #[error("numeric value exceeds integer bounds")]
    NumericOverflow(#[from] ParseIntError),
    #[error("invalid character {0:?} in data")]
    InvalidChar(char),
    #[error("input ended without reaching '!'")]
    UnexpectedEof,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct CommentParser<'a>(&'a str);

impl<'a> CommentParser<'a> {
    fn next_comment(&mut self) -> Result<Option<(char, &'a str)>, RleError> {
        let Some((line, rem)) =
            split_at_newline(self.0).and_then(|(ln, r)| Some((ln.strip_prefix('#')?, r)))
        else {
            return Ok(None);
        };
        let code = line.chars().next().ok_or(RleError::NoCode)?;
        let rest = &line[code.len_utf8()..];
        let text = rest.trim_start_matches(' ');
        if std::ptr::eq(rest, text) {
            return Err(RleError::NoSpaceAfterCode(code));
        }
        self.0 = rem;
        Ok(Some((code, text)))
    }

    fn into_inner(self) -> &'a str {
        self.0
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct RleItem {
    pub(crate) count: usize,
    pub(crate) tag: Tag,
}

impl RleItem {
    fn display_len(&self) -> usize {
        let digits = if self.count == 1 {
            0
        } else if let Some(x) = self.count.checked_ilog10() {
            let Ok(x) = usize::try_from(x) else {
                unreachable!("The number of digits in a usize should fit in a usize");
            };
            x + 1
        } else {
            // self.count == 0
            1
        };
        digits + 1
    }
}

impl fmt::Display for RleItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.count != 1 {
            write!(f, "{}", self.count)?;
        }
        write!(f, "{}", self.tag.symbol())?;
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum Tag {
    Dead,
    Live,
    Eol,
}

impl Tag {
    fn symbol(&self) -> char {
        match self {
            Tag::Dead => 'b',
            Tag::Live => 'o',
            Tag::Eol => '$',
        }
    }
}

fn parse_header(header: &str) -> Result<(usize, usize), RleError> {
    let mut scanner = Scanner::new(header);
    scanner.expect_char('x')?;
    scanner.skip_whitespace();
    scanner.expect_char('=')?;
    scanner.skip_whitespace();
    let width = scanner.scan_usize()?.ok_or(RleError::InvalidHeader)?;
    scanner.skip_whitespace();
    scanner.expect_char(',')?;
    scanner.skip_whitespace();
    scanner.expect_char('y')?;
    scanner.skip_whitespace();
    scanner.expect_char('=')?;
    scanner.skip_whitespace();
    let height = scanner.scan_usize()?.ok_or(RleError::InvalidHeader)?;
    if !scanner.is_empty() {
        scanner.skip_whitespace();
        scanner.expect_char(',')?;
        scanner.skip_whitespace();
        scanner.expect_str("rule")?;
        scanner.skip_whitespace();
        scanner.expect_char('=')?;
        scanner.skip_whitespace();
        scanner
            .expect_str("B3/S23")
            .map_err(|_| RleError::UnsupportedRule)?;
        if !scanner.is_empty() {
            return Err(RleError::InvalidHeader);
        }
    }
    Ok((width, height))
}

fn parse_runs(s: &str) -> Runs<'_> {
    Runs::new(s)
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Runs<'a>(Scanner<'a>);

impl<'a> Runs<'a> {
    fn new(s: &'a str) -> Runs<'a> {
        Runs(Scanner::new(s))
    }
}

impl Iterator for Runs<'_> {
    type Item = Result<(usize, Tag), RleError>;

    // Once this iterator yields `Err` or `None`, it is unsuitable for further
    // iteration.
    fn next(&mut self) -> Option<Self::Item> {
        self.0.skip_whitespace();
        if self.0.expect_char('!').is_ok() {
            return None;
        }
        let count = match self.0.scan_usize() {
            Ok(Some(count)) => count,
            Ok(None) => 1,
            Err(e) => return Some(Err(e.into())),
        };
        let tag = match self.0.scan_char() {
            Some('b' | 'B') => Tag::Dead,
            Some(c) if c.is_ascii_alphabetic() => Tag::Live,
            Some('$') => Tag::Eol,
            Some(c) => return Some(Err(RleError::InvalidChar(c))),
            None => return Some(Err(RleError::UnexpectedEof)),
        };
        Some(Ok((count, tag)))
    }
}

impl FusedIterator for Runs<'_> {}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct Scanner<'a>(&'a str);

impl<'a> Scanner<'a> {
    fn new(s: &'a str) -> Scanner<'a> {
        Scanner(s)
    }

    fn skip_whitespace(&mut self) {
        self.0 = self.0.trim_start();
    }

    fn scan_char(&mut self) -> Option<char> {
        let c = self.0.chars().next()?;
        self.0 = &self.0[c.len_utf8()..];
        Some(c)
    }

    fn expect_char(&mut self, c: char) -> Result<(), RleError> {
        if let Some(t) = self.0.strip_prefix(c) {
            self.0 = t;
            Ok(())
        } else {
            Err(RleError::InvalidHeader)
        }
    }

    fn expect_str(&mut self, s: &str) -> Result<(), RleError> {
        if let Some(t) = self.0.strip_prefix(s) {
            self.0 = t;
            Ok(())
        } else {
            Err(RleError::InvalidHeader)
        }
    }

    fn scan_usize(&mut self) -> Result<Option<usize>, ParseIntError> {
        let Some((digits, s)) = scan_some(self.0, |c| c.is_ascii_digit()) else {
            return Ok(None);
        };
        let value = digits.parse::<usize>()?;
        self.0 = s;
        Ok(Some(value))
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn glider() {
        let s = "#C This is a glider.\nx = 3, y = 3\nbo$2bo$3o!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.comments, [('C', String::from("This is a glider."))]);
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(
            rle.to_string(),
            "#C This is a glider.\nx = 3, y = 3\nbo$2bo$3o$!\n"
        );
    }
}
