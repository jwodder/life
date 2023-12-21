use super::util::{ascii_lines, scan_some, split_at_newline};
use crate::{Edges, Pattern};
use std::fmt;
use std::iter::FusedIterator;
use std::num::ParseIntError;
use std::str::FromStr;
use thiserror::Error;

/// A pattern represented in the [run length encoded file
/// format](https://conwaylife.com/wiki/Run_Length_Encoded)
///
/// An `Rle` instance can be constructed from an RLE string via [`FromStr`] and
/// converted to the RLE format via [`Display`][fmt::Display] (which includes a
/// trailing newline).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rle {
    /// A list of `#` lines present in the RLE encoding, represented as pairs
    /// of a type letter and text
    ///
    /// When displaying an `Rle` instance, if the text in an element of
    /// `comments` contains one or more non-final newlines, each line in the
    /// text will be converted to a separate `#` line with the same type
    /// letter.  If the text ends in a newline, that newline is ignored.
    pub comments: Vec<(char, String)>,

    /// The pattern itself
    pub pattern: Pattern,
}

impl fmt::Display for Rle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (ty, text) in &self.comments {
            for ln in ascii_lines(text) {
                writeln!(f, "#{ty} {ln}")?;
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

    /// Parse a pattern given in RLE format.
    ///
    /// # Errors
    ///
    /// See [`RleError`] for the various error conditions.
    ///
    /// # Implementation-Specific Parsing Details
    ///
    /// This implementation makes the following decisions about how to parse
    /// the RLE format:
    ///
    /// - A `#` line must consist of, in order, a `#`, any single non-newline
    ///   character, one or more space (U+0020) characters (discarded), and
    ///   freeform text.
    ///
    /// - Blank lines (containing no characters other than Unicode whitespace)
    ///   are permitted between the `#` lines (if any) and the header line.
    ///
    /// - Tokens in the header line may be surrounded by zero or more Unicode
    ///   whitespace characters other than newline sequences.
    ///
    /// - The header line may contain an optional "rule" field, but it must
    ///   equal `B3/S23` (case insensitive) or `23/3`.
    ///
    /// - Tokens in the pattern data may be separated by zero or more Unicode
    ///   whitespace characters.
    ///
    /// - Specifications for cells outside the width & height given in the
    ///   header are accepted but ignored.
    ///
    /// - 'b' and 'B' are parsed as dead cells.  All other ASCII letters are
    ///   parsed as live cells.
    fn from_str(s: &str) -> Result<Rle, RleError> {
        let mut cparser = CommentParser(s);
        let mut comments = Vec::new();
        while let Some((ty, text)) = cparser.next_comment()? {
            comments.push((ty, text.to_owned()));
        }
        let s = cparser.into_inner().trim_start();
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
                Tag::Live => {
                    pattern.set_run(y, x, count, true);
                    x += count;
                }
                Tag::Eol => {
                    y += count;
                    x = 0;
                }
            }
        }
        Ok(Rle { comments, pattern })
    }
}

impl From<Rle> for Pattern {
    fn from(value: Rle) -> Pattern {
        value.pattern
    }
}

#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum RleError {
    /// Returned if a `#` line does not have a non-newline character
    /// immediately after the `#`.
    #[error("'#' line lacks type character")]
    NoType,

    /// Returned if the character after the `#` at the start of a `#` line is
    /// not followed by one or more space characters
    #[error("no space after {0:?} type in '#' line")]
    NoSpaceAfterType(char),

    /// Returned if the input did not contain any characters outside of `#`
    /// lines
    #[error("no data in RLE input")]
    NoData,

    /// Returned if the header line was malformed
    #[error("invalid header line")]
    InvalidHeader,

    /// Returned if the header line specified a rule other than Conway's Game
    /// of Life
    #[error("header specifies unsupported rule")]
    UnsupportedRule,

    /// Returned if a number in the header or data exceeded [`usize::MAX`]
    #[error("numeric value exceeds integer bounds")]
    NumericOverflow(#[from] ParseIntError),

    /// Returned if whitespace is encountered after an RLE count
    #[error("space after RLE count")]
    SpaceAfterCount,

    /// Returned if an invalid character was encountered in the data
    #[error("invalid character {0:?} in data")]
    InvalidChar(char),

    /// Returned if the end of input was reached without encountering a `!`
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
        let ty = line.chars().next().ok_or(RleError::NoType)?;
        let rest = &line[ty.len_utf8()..];
        let text = rest.trim_start_matches(' ');
        if std::ptr::eq(rest, text) {
            return Err(RleError::NoSpaceAfterType(ty));
        }
        self.0 = rem;
        Ok(Some((ty, text)))
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
    scanner.skip_whitespace();
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
    scanner.skip_whitespace();
    if !scanner.is_empty() {
        scanner.expect_char(',')?;
        scanner.skip_whitespace();
        scanner.expect_str("rule")?;
        scanner.skip_whitespace();
        scanner.expect_char('=')?;
        scanner.skip_whitespace();
        scanner
            .expect_str_ignore_ascii_case("B3/S23")
            .or_else(|_| scanner.expect_str("23/3"))
            .map_err(|_| RleError::UnsupportedRule)?;
        scanner.skip_whitespace();
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
            Some(c) if c.is_whitespace() => return Some(Err(RleError::SpaceAfterCount)),
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

    fn expect_str_ignore_ascii_case(&mut self, s: &str) -> Result<(), RleError> {
        if self
            .0
            .get(0..s.len())
            .is_some_and(|t| t.eq_ignore_ascii_case(s))
        {
            self.0 = &self.0[s.len()..];
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
    use crate::PatternParser;

    #[test]
    fn glider() {
        let s = "#C This is a glider.\nx = 3, y = 3\nbo$2bo$3o!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.comments, [('C', String::from("This is a glider."))]);
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(rle.to_string(), s);
    }

    #[test]
    fn ragged() {
        let s = concat!(
            "#N beehiveoncap.rle\n",
            "#C https://conwaylife.com/wiki/Beehive_on_cap\n",
            "#C https://www.conwaylife.com/patterns/beehiveoncap.rle\n",
            "x = 5, y = 7, rule = B3/S23\n",
            "b2o$o2bo$4o2$2b2o$bo2bo$2b2o!\n",
        );
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(
            rle.comments,
            [
                ('N', String::from("beehiveoncap.rle")),
                (
                    'C',
                    String::from("https://conwaylife.com/wiki/Beehive_on_cap")
                ),
                (
                    'C',
                    String::from("https://www.conwaylife.com/patterns/beehiveoncap.rle")
                ),
            ]
        );
        assert_eq!(
            rle.pattern.draw('.', 'O').to_string(),
            ".OO..\nO..O.\nOOOO.\n.....\n..OO.\n.O..O\n..OO."
        );
        assert_eq!(
            rle.to_string(),
            concat!(
                "#N beehiveoncap.rle\n",
                "#C https://conwaylife.com/wiki/Beehive_on_cap\n",
                "#C https://www.conwaylife.com/patterns/beehiveoncap.rle\n",
                "x = 5, y = 7\n",
                "b2o$o2bo$4o2$2b2o$bo2bo$2b2o!\n",
            )
        );
    }

    #[test]
    fn line_wrapping() {
        let s = concat!(
            "#N zebrastripes.rle\n",
            "#C https://conwaylife.com/wiki/Zebra_stripes\n",
            "#C https://www.conwaylife.com/patterns/zebrastripes.rle\n",
            "x = 27, y = 21, rule = B3/S23\n",
            "2b2o$2bo$4bo2bo2bo2bo2bo2bo2bo$3b20o$2bo$3b18o$21bo$b20o$o$b22o$23bob\n",
            "2o$b20o2bob2o$o20bobo$b20o2bo$23b2o$3b18o$2bo18bo$3b18o2$5b2o2b2obob4o\n",
            "b2o$5b2o2bob2obo2bob2o!\n",
        );
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(
            rle.pattern.draw('.', 'O').to_string(),
            concat!(
                "..OO.......................\n",
                "..O........................\n",
                "....O..O..O..O..O..O..O....\n",
                "...OOOOOOOOOOOOOOOOOOOO....\n",
                "..O........................\n",
                "...OOOOOOOOOOOOOOOOOO......\n",
                ".....................O.....\n",
                ".OOOOOOOOOOOOOOOOOOOO......\n",
                "O..........................\n",
                ".OOOOOOOOOOOOOOOOOOOOOO....\n",
                ".......................O.OO\n",
                ".OOOOOOOOOOOOOOOOOOOO..O.OO\n",
                "O....................O.O...\n",
                ".OOOOOOOOOOOOOOOOOOOO..O...\n",
                ".......................OO..\n",
                "...OOOOOOOOOOOOOOOOOO......\n",
                "..O..................O.....\n",
                "...OOOOOOOOOOOOOOOOOO......\n",
                "...........................\n",
                ".....OO..OO.O.OOOO.OO......\n",
                ".....OO..O.OO.O..O.OO......",
            )
        );
        assert_eq!(
            rle.to_string(),
            concat!(
                "#N zebrastripes.rle\n",
                "#C https://conwaylife.com/wiki/Zebra_stripes\n",
                "#C https://www.conwaylife.com/patterns/zebrastripes.rle\n",
                "x = 27, y = 21\n",
                "2b2o$2bo$4bo2bo2bo2bo2bo2bo2bo$3b20o$2bo$3b18o$21bo$b20o$o$b22o$23bob\n",
                "2o$b20o2bob2o$o20bobo$b20o2bo$23b2o$3b18o$2bo18bo$3b18o2$5b2o2b2obob4o\n",
                "b2o$5b2o2bob2obo2bob2o!\n",
            )
        );
    }

    #[test]
    fn all_dead() {
        let s = "x = 5, y = 5\n!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(
            rle.pattern.draw('.', 'O').to_string(),
            ".....\n.....\n.....\n.....\n....."
        );
        assert_eq!(rle.to_string(), s);
    }

    #[test]
    fn empty() {
        let s = "x = 0, y = 0\n!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), "");
        assert_eq!(rle.to_string(), s);
    }

    #[test]
    fn dot() {
        let s = "x = 1, y = 1\no!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), "O");
        assert_eq!(rle.to_string(), s);
    }

    #[test]
    fn out_of_bounds() {
        let s = "x = 3, y = 3\nbo3b2o$2b3o$3o$2ob!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(rle.to_string(), "x = 3, y = 3\nbo$2bo$3o!\n");
    }

    #[test]
    fn spaced_data() {
        let s = "x = 3, y = 3\n b  o  $ 2b o \n $ 3o\n!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(rle.to_string(), "x = 3, y = 3\nbo$2bo$3o!\n");
    }

    #[test]
    fn leading_trailing_blank_lines() {
        let s = "x = 3, y = 5\n$bo$2bo$3o!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(
            rle.pattern.draw('.', 'O').to_string(),
            "...\n.O.\n..O\nOOO\n..."
        );
        assert_eq!(rle.to_string(), s);
    }

    #[test]
    fn alternative_letters() {
        let s = "x = 3, y = 3\nBO$2bq\n$3L\n!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(rle.to_string(), "x = 3, y = 3\nbo$2bo$3o!\n");
    }

    #[test]
    fn empty_comment() {
        let s = "#C \nx = 3, y = 3\nbo$2bo$3o!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.comments, [('C', String::new())]);
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(rle.to_string(), "#C \nx = 3, y = 3\nbo$2bo$3o!\n");
    }

    #[test]
    fn whitespace_comment() {
        let s = "#C  \nx = 3, y = 3\nbo$2bo$3o!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.comments, [('C', String::new())]);
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(rle.to_string(), "#C \nx = 3, y = 3\nbo$2bo$3o!\n");
    }

    #[test]
    fn lowercase_rule() {
        let s = concat!(
            "#N Hooks\n",
            "#C A period 5 oscillator.\n",
            "#C www.conwaylife.com/wiki/Hooks\n",
            "x = 11, y = 10, rule = b3/s23\n",
            "6b2o3b$ob2obobo3b$2obobo5b$4b2o5b$5bo5b2$7b2o2b$7bo3b$8b3o$10bo!\n",
        );
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(
            rle.pattern.draw('.', 'O').to_string(),
            concat!(
                "......OO...\n",
                "O.OO.O.O...\n",
                "OO.O.O.....\n",
                "....OO.....\n",
                ".....O.....\n",
                "...........\n",
                ".......OO..\n",
                ".......O...\n",
                "........OOO\n",
                "..........O",
            )
        );
        assert_eq!(
            rle.to_string(),
            concat!(
                "#N Hooks\n",
                "#C A period 5 oscillator.\n",
                "#C www.conwaylife.com/wiki/Hooks\n",
                "x = 11, y = 10\n",
                "6b2o$ob2obobo$2obobo$4b2o$5bo2$7b2o$7bo$8b3o$10bo!\n",
            )
        );
    }

    #[test]
    fn sb_rule_and_blanks_before_header() {
        let s = concat!(
            "#N tubwithnine.rle\n",
            "#C https://conwaylife.com/wiki/Tub_with_nine\n",
            "#C https://www.conwaylife.com/patterns/tubwithnine.rle\n",
            "\n",
            "\n",
            "x = 6, y = 6, rule = 23/3\n",
            "2o4b$obo3b$2bo3b$2bobob$3bobo$4bo!\n",
        );
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(
            rle.pattern.draw('.', 'O').to_string(),
            "OO....\nO.O...\n..O...\n..O.O.\n...O.O\n....O."
        );
        assert_eq!(
            rle.to_string(),
            concat!(
                "#N tubwithnine.rle\n",
                "#C https://conwaylife.com/wiki/Tub_with_nine\n",
                "#C https://www.conwaylife.com/patterns/tubwithnine.rle\n",
                "x = 6, y = 6\n",
                "2o$obo$2bo$2bobo$3bobo$4bo!\n",
            )
        );
    }

    #[test]
    fn unspaced_header() {
        let s = "x=3,y=3\nbo$2bo$3o!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(rle.to_string(), "x = 3, y = 3\nbo$2bo$3o!\n");
    }

    #[test]
    fn extra_spaced_header() {
        let s = " x  =  3  ,  y  =  3  \nbo$2bo$3o!\n";
        let rle = s.parse::<Rle>().unwrap();
        assert_eq!(rle.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(rle.to_string(), "x = 3, y = 3\nbo$2bo$3o!\n");
    }

    #[test]
    fn multiline_comment() {
        let rle = Rle {
            comments: vec![('C', String::from("Line 1\nLine 2\n"))],
            pattern: PatternParser::dead_chars(" .").parse(".#.\n..#\n###\n"),
        };
        assert_eq!(
            rle.to_string(),
            "#C Line 1\n#C Line 2\nx = 3, y = 3\nbo$2bo$3o!\n"
        );
    }

    mod parse_err {
        use super::*;
        use assert_matches::assert_matches;

        #[test]
        fn textless_comment() {
            let s = "#C\nx = 3, y = 3\nbo$2bo$3o!\n";
            let e = s.parse::<Rle>().unwrap_err();
            assert_eq!(e, RleError::NoSpaceAfterType('C'));
            assert_eq!(e.to_string(), "no space after 'C' type in '#' line");
        }

        #[test]
        fn embedded_comment() {
            let s = "x = 3, y = 3\nbo$2bo$\n#C \\o/!\n3o!\n";
            let e = s.parse::<Rle>().unwrap_err();
            assert_eq!(e, RleError::InvalidChar('#'));
            assert_eq!(e.to_string(), "invalid character '#' in data");
        }

        #[test]
        fn count_space_tag() {
            let s = "x = 3, y = 3\nbo$ 2 b o$3o!\n";
            let e = s.parse::<Rle>().unwrap_err();
            assert_eq!(e, RleError::SpaceAfterCount);
            assert_eq!(e.to_string(), "space after RLE count");
        }

        #[test]
        fn codeless_comment() {
            let s = "#\nx = 3, y = 3\nbo$ 2 b o$3o!\n";
            let e = s.parse::<Rle>().unwrap_err();
            assert_eq!(e, RleError::NoType);
            assert_eq!(e.to_string(), "'#' line lacks type character");
        }

        #[test]
        fn nodata() {
            let s = "#C Oops, forgot the pattern!\n";
            let e = s.parse::<Rle>().unwrap_err();
            assert_eq!(e, RleError::NoData);
            assert_eq!(e.to_string(), "no data in RLE input");
        }

        #[test]
        fn backwards_header() {
            let s = "y = 3, x = 3\nbo$2bo$3o!\n";
            let e = s.parse::<Rle>().unwrap_err();
            assert_eq!(e, RleError::InvalidHeader);
            assert_eq!(e.to_string(), "invalid header line");
        }

        #[test]
        fn unsupported_rule() {
            let s = concat!(
                "#N nontnosedp15.rle\n",
                "#C https://conwaylife.com/wiki/T-nose\n",
                "#C https://www.conwaylife.com/patterns/nontnosedp15.rle\n",
                "#C (LifeHistory highlighted version)\n",
                "x = 3, y = 16, rule = LifeHistory\n",
                ".E$.A$3A3$3A$.A$.A$.A$.A$3A3$3A$.A$.A!\n",
            );
            let e = s.parse::<Rle>().unwrap_err();
            assert_eq!(e, RleError::UnsupportedRule);
            assert_eq!(e.to_string(), "header specifies unsupported rule");
        }

        #[test]
        fn extra_header_field() {
            let s = "x = 3, y = 3, coolness = 20\nbo$2bo$3o!\n";
            let e = s.parse::<Rle>().unwrap_err();
            assert_eq!(e, RleError::InvalidHeader);
            assert_eq!(e.to_string(), "invalid header line");
        }

        #[cfg(any(
            target_pointer_width = "16",
            target_pointer_width = "32",
            target_pointer_width = "64"
        ))]
        #[test]
        fn giant_dimension() {
            let s = "x = 18446744073709551616, y = 3\nbo$2bo$3o!\n";
            let e = s.parse::<Rle>().unwrap_err();
            assert_matches!(e, RleError::NumericOverflow(_));
            assert_eq!(e.to_string(), "numeric value exceeds integer bounds");
        }

        #[cfg(any(
            target_pointer_width = "16",
            target_pointer_width = "32",
            target_pointer_width = "64"
        ))]
        #[test]
        fn giant_count() {
            let s = "x = 3, y = 3\nbo$18446744073709551616bo$3o!\n";
            let e = s.parse::<Rle>().unwrap_err();
            assert_matches!(e, RleError::NumericOverflow(_));
            assert_eq!(e.to_string(), "numeric value exceeds integer bounds");
        }

        #[test]
        fn missing_bang() {
            let s = "x = 3, y = 3\nbo$2bo$3o\n";
            let e = s.parse::<Rle>().unwrap_err();
            assert_eq!(e, RleError::UnexpectedEof);
            assert_eq!(e.to_string(), "input ended without reaching '!'");
        }

        #[test]
        fn just_header() {
            let s = "x = 3, y = 3";
            let e = s.parse::<Rle>().unwrap_err();
            assert_eq!(e, RleError::UnexpectedEof);
            assert_eq!(e.to_string(), "input ended without reaching '!'");
        }
    }
}
