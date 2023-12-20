use super::util::ascii_lines;
use crate::{Pattern, PatternBuilder};
use std::fmt;
use std::str::FromStr;
use thiserror::Error;

/// A pattern represented in the [plaintext file
/// format](https://conwaylife.com/wiki/Plaintext)
///
/// A `Plaintext` instance can be constructed from a plaintext string via
/// [`FromStr`] and converted to the plaintext format via
/// [`Display`][fmt::Display] (which includes a trailing newline).
///
/// # Format
///
/// The plaintext file format encodes a Game of Life pattern as follows:
///
/// - The first line must start with `"!Name:"`.  The rest of the line is a
///   name for the pattern.
///
///   - This implementation requires that the colon be followed by one or more
///     space (U+0020) characters, all of which are discarded when parsing.
///
///   - This implementation accepts empty names.
///
/// - After the first line, there may be any number of comment lines, each of
///   which begins with an exclamation point (`!`), which is discarded when
///   parsing.
///
/// - The remaining lines define the pattern itself via an ASCII drawing.  Each
///   row of the pattern is represented as a line in which `.` denotes a dead
///   cell and `O` denotes a live cell.
///
///   - Drawings in which not all lines are of the same length are accepted but
///     discouraged.
///
///   - Blank lines in a drawing (denoting rows composed entirely of dead
///     cells) are accepted but discouraged.
///
///   - This implementation does not accept any characters other than `.`, `O`,
///     and newlines in a drawing.  In particular, comments may not occur in
///     the middle of a drawing.
///
/// - This implementation recognizes only LF, CR, and CR LF as newline
///   sequences.
///
/// A plaintext encoding of the [glider](https://conwaylife.com/wiki/Glider):
///
/// ```text
/// !Name: Glider
/// !Very famous.
/// .O.
/// ..O
/// OOO
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Plaintext {
    /// Name of the pattern
    ///
    /// When displaying a `Plaintext` instance, if `name` contains one or more
    /// non-final newlines, each line in `name` after the first will be
    /// converted to a comment.  If `name` ends in a newline, that newline is
    /// ignored.
    pub name: String,

    /// Comments on the pattern
    ///
    /// When displaying a `Plaintext` instance, if an element of `comments`
    /// contains one or more non-final newlines, each line of the element is
    /// converted to a separate comment.  If an element ends in a newline, that
    /// newline is ignored.
    pub comments: Vec<String>,

    /// The pattern itself
    pub pattern: Pattern,
}

impl fmt::Display for Plaintext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut namelines = ascii_lines(&self.name);
        let Some(name) = namelines.next() else {
            unreachable!("ascii_lines() should yield at least one element");
        };
        writeln!(f, "!Name: {name}")?;
        for ln in namelines {
            writeln!(f, "!{ln}")?;
        }
        for c in &self.comments {
            for ln in ascii_lines(c) {
                writeln!(f, "!{ln}")?;
            }
        }
        writeln!(f, "{}", self.pattern.draw('.', 'O'))?;
        Ok(())
    }
}

impl FromStr for Plaintext {
    type Err = PlaintextError;

    /// Parse a pattern given in plaintext format.
    ///
    /// # Errors
    ///
    /// `Err` is returned if the input does not begin with `"!Name: "` or if
    /// the pattern drawing contains any characters other than `.`, `O`, and
    /// newline sequences.
    fn from_str(s: &str) -> Result<Plaintext, PlaintextError> {
        let mut lines = ascii_lines(s);
        let name = lines
            .next()
            .and_then(|ln| ln.strip_prefix("!Name: "))
            .ok_or(PlaintextError::NoName)?
            .trim_start_matches(' ');
        let mut comments = Vec::new();
        let mut builder = PatternBuilder::new();
        let mut y = 0;
        for ln in lines {
            if let Some(comm) = ln.strip_prefix('!') {
                if y == 0 {
                    comments.push(String::from(comm));
                } else {
                    return Err(PlaintextError::InvalidChar('!'));
                }
            } else {
                for (x, ch) in ln.chars().enumerate() {
                    // Ensure that trailing dead cells count towards the width:
                    builder = builder.min_width(x.saturating_add(1));
                    match ch {
                        'O' => builder.push(y, x),
                        '.' => (),
                        ch => return Err(PlaintextError::InvalidChar(ch)),
                    }
                }
                y += 1;
            }
        }
        // Ensure that trailing dead rows count towards the height:
        eprintln!("Setting min height to {y}");
        builder = builder.min_height(y);
        Ok(Plaintext {
            name: String::from(name),
            comments,
            pattern: builder.build(),
        })
    }
}

#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum PlaintextError {
    /// Returned if the input does not start with `"!Name: "`
    #[error(r#"plaintext input does not start with "!Name:" line"#)]
    NoName,

    /// Returned if the pattern drawing contains any characters other than `.`,
    /// `O`, and newline sequences
    #[error("plaintext drawing contains invalid character {0:?}")]
    InvalidChar(char),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PatternParser;

    #[test]
    fn glider() {
        let s = "!Name: Glider\n!\n.O.\n..O\nOOO\n";
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name, "Glider");
        assert_eq!(pt.comments, [""]);
        assert_eq!(pt.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(pt.to_string(), s);
    }

    #[test]
    fn empty() {
        let s = "!Name: Empty\n";
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name, "Empty");
        assert!(pt.comments.is_empty());
        assert_eq!(pt.pattern.height(), 0);
        assert_eq!(pt.pattern.draw('.', 'O').to_string(), "");
        assert_eq!(pt.to_string(), "!Name: Empty\n\n");
    }

    #[test]
    fn dot() {
        let s = "!Name: Dot\n.\n";
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name, "Dot");
        assert!(pt.comments.is_empty());
        assert_eq!(pt.pattern.draw('.', 'O').to_string(), ".");
        assert_eq!(pt.to_string(), s);
    }

    #[test]
    fn ragged() {
        let s = concat!(
            "!Name: Acorn\n",
            "!Author: Charles Corderman\n",
            "!A methuselah that stabilizes after 5206 generations.\n",
            "!www.conwaylife.com/wiki/index.php?title=Acorn\n",
            ".O\n",
            "...O\n",
            "OO..OOO\n",
        );
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name, "Acorn");
        assert_eq!(
            pt.comments,
            [
                "Author: Charles Corderman",
                "A methuselah that stabilizes after 5206 generations.",
                "www.conwaylife.com/wiki/index.php?title=Acorn",
            ]
        );
        assert_eq!(
            pt.pattern.draw('.', 'O').to_string(),
            ".O.....\n...O...\nOO..OOO"
        );
        assert_eq!(
            pt.to_string(),
            concat!(
                "!Name: Acorn\n",
                "!Author: Charles Corderman\n",
                "!A methuselah that stabilizes after 5206 generations.\n",
                "!www.conwaylife.com/wiki/index.php?title=Acorn\n",
                ".O.....\n",
                "...O...\n",
                "OO..OOO\n",
            )
        );
    }

    #[test]
    fn leading_trailing_blank_lines() {
        let s = "!Name: Glider\n\n.O.\n..O\nOOO\n\n";
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name, "Glider");
        assert!(pt.comments.is_empty());
        assert_eq!(
            pt.pattern.draw('.', 'O').to_string(),
            "...\n.O.\n..O\nOOO\n..."
        );
        assert_eq!(pt.to_string(), "!Name: Glider\n...\n.O.\n..O\nOOO\n...\n");
    }

    #[test]
    #[rustfmt::skip]
    fn middle_blank_line() {
        let s = concat!(
            "!Name: Beehive and dock\n",
            "!https://conwaylife.com/ref/lexicon/lex_b.htm#beehiveanddock\n",
            "...OO\n",
            "..O..O\n",
            "...OO\n",
            "\n",
            ".OOOO\n",
            "O....O\n",
            "OO..OO\n",
        );
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name, "Beehive and dock");
        assert_eq!(pt.comments, ["https://conwaylife.com/ref/lexicon/lex_b.htm#beehiveanddock"]);
        assert_eq!(
            pt.pattern.draw('.', 'O').to_string(),
            concat!(
                "...OO.\n",
                "..O..O\n",
                "...OO.\n",
                "......\n",
                ".OOOO.\n",
                "O....O\n",
                "OO..OO",
            )
        );
        assert_eq!(pt.to_string(), concat!(
            "!Name: Beehive and dock\n",
            "!https://conwaylife.com/ref/lexicon/lex_b.htm#beehiveanddock\n",
            "...OO.\n",
            "..O..O\n",
            "...OO.\n",
            "......\n",
            ".OOOO.\n",
            "O....O\n",
            "OO..OO\n",
        ));
    }

    #[test]
    fn embedded_comment() {
        let s = "!Name: Glider\n.O.\n..O\n!Oh!\nOOO\n";
        let e = s.parse::<Plaintext>().unwrap_err();
        assert_eq!(e, PlaintextError::InvalidChar('!'));
        assert_eq!(
            e.to_string(),
            "plaintext drawing contains invalid character '!'"
        );
    }

    #[test]
    fn one_blank_line() {
        let s = "!Name: Blank line\n\n";
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name, "Blank line");
        assert!(pt.comments.is_empty());
        assert_eq!(pt.pattern.height(), 0);
        assert_eq!(pt.pattern.draw('.', 'O').to_string(), "");
        assert_eq!(pt.to_string(), s);
    }

    #[test]
    fn display_multiline_name() {
        let pt = Plaintext {
            name: String::from("Line 1\nLine 2"),
            comments: Vec::new(),
            pattern: PatternParser::dead_chars(" .").parse(".#.\n..#\n###\n"),
        };
        assert_eq!(pt.to_string(), "!Name: Line 1\n!Line 2\n.O.\n..O\nOOO\n");
    }

    #[test]
    fn display_multiline_comment() {
        let pt = Plaintext {
            name: String::from("Pattern"),
            comments: vec![String::from("Line 1\nLine 2")],
            pattern: PatternParser::dead_chars(" .").parse(".#.\n..#\n###\n"),
        };
        assert_eq!(
            pt.to_string(),
            "!Name: Pattern\n!Line 1\n!Line 2\n.O.\n..O\nOOO\n"
        );
    }

    #[test]
    fn display_empty_name_and_comment() {
        let pt = Plaintext {
            name: String::new(),
            comments: vec![String::new()],
            pattern: PatternParser::dead_chars(" .").parse(".#.\n..#\n###\n"),
        };
        assert_eq!(pt.to_string(), "!Name: \n!\n.O.\n..O\nOOO\n");
    }
}
