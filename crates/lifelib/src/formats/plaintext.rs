use super::util::ascii_lines;
use crate::errors::ParseLineError;
use crate::utilities::Line;
use crate::{Pattern, PatternBuilder};
use std::fmt;
use std::str::FromStr;
use thiserror::Error;

/// A pattern represented in the [plaintext file
/// format](https://conwaylife.com/wiki/Plaintext).  The exact format accepted
/// by `lifelib` is described in [`doc/plaintext.md`][1].
///
/// [1]: https://github.com/jwodder/life/blob/master/doc/plaintext.md
///
/// A `Plaintext` instance can be constructed from a plaintext string via
/// [`FromStr`] and converted to the plaintext format via
/// [`Display`][fmt::Display] (which includes a trailing newline).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Plaintext {
    /// Name of the pattern
    pub name: Option<Line>,

    /// Comments on the pattern
    pub comments: Vec<Line>,

    /// The pattern itself
    pub pattern: Pattern,
}

impl fmt::Display for Plaintext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref name) = self.name {
            writeln!(f, "!Name: {name}")?;
        }
        for c in &self.comments {
            writeln!(f, "!{c}")?;
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
        let mut name = None;
        let mut comments = Vec::new();
        let mut builder = PatternBuilder::new();
        let mut y = 0;
        for ln in ascii_lines(s) {
            if let Some(comm) = ln.strip_prefix('!') {
                if y == 0 {
                    match (
                        comments.is_empty() && name.is_none(),
                        comm.strip_prefix("Name: "),
                    ) {
                        (true, Some(n)) => {
                            name = Some(n.trim_start_matches(' ').parse::<Line>()?);
                        }
                        _ => comments.push(comm.parse::<Line>()?),
                    }
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
        builder = builder.min_height(y);
        Ok(Plaintext {
            name,
            comments,
            pattern: builder.build(),
        })
    }
}

impl From<Plaintext> for Pattern {
    fn from(value: Plaintext) -> Pattern {
        value.pattern
    }
}

#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum PlaintextError {
    /// Returned if a comment (including the "Name:" line) contains an "exotic"
    /// newline character
    #[error(r#"comment contains forbidden "exotic" newline {:?}"#, .0.0)]
    NewlineInComment(#[from] ParseLineError),

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
        assert_eq!(pt.name.as_ref().unwrap(), "Glider");
        assert_eq!(pt.comments, [""]);
        assert_eq!(pt.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(pt.to_string(), s);
    }

    #[test]
    fn empty() {
        let s = "!Name: Empty\n";
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name.as_ref().unwrap(), "Empty");
        assert!(pt.comments.is_empty());
        assert_eq!(pt.pattern.height(), 0);
        assert_eq!(pt.pattern.draw('.', 'O').to_string(), "");
        assert_eq!(pt.to_string(), "!Name: Empty\n\n");
    }

    #[test]
    fn dot() {
        let s = "!Name: Dot\n.\n";
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name.as_ref().unwrap(), "Dot");
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
        assert_eq!(pt.name.as_ref().unwrap(), "Acorn");
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
        assert_eq!(pt.name.as_ref().unwrap(), "Glider");
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
        assert_eq!(pt.name.as_ref().unwrap(), "Beehive and dock");
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
        assert_eq!(pt.name.as_ref().unwrap(), "Blank line");
        assert!(pt.comments.is_empty());
        assert_eq!(pt.pattern.height(), 0);
        assert_eq!(pt.pattern.draw('.', 'O').to_string(), "");
        assert_eq!(pt.to_string(), s);
    }

    #[test]
    fn display_empty_name_and_comment() {
        let pt = Plaintext {
            name: Some("".parse::<Line>().unwrap()),
            comments: vec!["".parse::<Line>().unwrap()],
            pattern: PatternParser::dead_chars(" .").parse(".#.\n..#\n###\n"),
        };
        assert_eq!(pt.to_string(), "!Name: \n!\n.O.\n..O\nOOO\n");
    }

    #[test]
    fn no_name() {
        let s = ".O.\n..O\nOOO\n";
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name, None);
        assert!(pt.comments.is_empty());
        assert_eq!(pt.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(pt.to_string(), s);
    }

    #[test]
    fn comment_no_name() {
        let s = "!Glider\n.O.\n..O\nOOO\n";
        let pt = s.parse::<Plaintext>().unwrap();
        assert_eq!(pt.name, None);
        assert_eq!(pt.comments, ["Glider"]);
        assert_eq!(pt.pattern.draw('.', 'O').to_string(), ".O.\n..O\nOOO");
        assert_eq!(pt.to_string(), s);
    }

    #[test]
    fn bad_newline_in_name() {
        let s = "!Name: Glider\x0B\n.O.\n..O\nOOO\n";
        let e = s.parse::<Plaintext>().unwrap_err();
        assert_eq!(e, PlaintextError::NewlineInComment(ParseLineError('\x0B')));
        assert_eq!(
            e.to_string(),
            r#"comment contains forbidden "exotic" newline '\u{b}'"#
        );
    }

    #[test]
    fn bad_newline_in_comment() {
        let s = "!Pattern:\x0CGlider\x0B\n.O.\n..O\nOOO\n";
        let e = s.parse::<Plaintext>().unwrap_err();
        assert_eq!(e, PlaintextError::NewlineInComment(ParseLineError('\x0C')));
        assert_eq!(
            e.to_string(),
            r#"comment contains forbidden "exotic" newline '\u{c}'"#
        );
    }
}
