use crate::{
    Pattern,
    formats::{Format, Letter, Plaintext, PlaintextError, PlaintextRef, Rle, RleError, RleRef},
    utilities::Line,
};
use std::fmt;
use std::io::{BufWriter, Write};
use std::path::Path;
use thiserror::Error;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Document {
    /// Name of the pattern
    pub name: Option<Line>,

    /// Comments on the pattern
    pub comments: Vec<Line>,

    /// Additional RLE #-lines to include when converting to RLE.  Lines with
    /// type [`Letter::NAME_TYPE`], [`Letter::COMMENT_TYPE`], or
    /// [`Letter::ALT_COMMENT_TYPE`] should not be present here.
    pub rle_comments: Vec<(Letter, Line)>,

    /// The pattern itself
    pub pattern: Pattern,
}

impl Document {
    pub fn display(&self, format: Format) -> DisplayDocument<'_> {
        DisplayDocument { doc: self, format }
    }

    pub fn load_from_str(s: &str, fc: FormatChoice) -> Result<Document, ParseDocumentError> {
        let format = match fc {
            FormatChoice::Autodetect => {
                Format::detect(s).ok_or(ParseDocumentError::AutodetectFailed)?
            }
            FormatChoice::Fixed(f) => f,
        };
        match format {
            Format::Plaintext => Ok(s.parse::<Plaintext>()?.into()),
            Format::Rle => Ok(s.parse::<Rle>()?.into()),
        }
    }

    pub fn load_from_file<P: AsRef<Path>>(
        p: P,
        fc: FormatChoice,
    ) -> Result<Document, ReadDocumentError> {
        let format = match fc {
            FormatChoice::Autodetect => {
                Format::identify(&p).ok_or(ReadDocumentError::AutodetectFailed)?
            }
            FormatChoice::Fixed(f) => f,
        };
        let s = std::fs::read_to_string(p)?;
        match format {
            Format::Plaintext => Ok(s.parse::<Plaintext>()?.into()),
            Format::Rle => Ok(s.parse::<Rle>()?.into()),
        }
    }

    pub fn dump_to_file(&self, p: &Path, fc: FormatChoice) -> Result<(), DumpDocumentError> {
        let format = match fc {
            FormatChoice::Autodetect => {
                Format::identify(p).ok_or(DumpDocumentError::AutodetectFailed)?
            }
            FormatChoice::Fixed(f) => f,
        };
        let mut fp = BufWriter::new(std::fs::File::create(p)?);
        write!(&mut fp, "{}", self.display(format))?;
        fp.flush()?;
        Ok(())
    }

    fn make_rle_comments(&self) -> Vec<(Letter, Line)> {
        let mut comments = Vec::with_capacity(
            self.comments
                .len()
                .saturating_add(self.rle_comments.len())
                .saturating_add(usize::from(self.name.is_some())),
        );
        if let Some(name) = self.name.clone() {
            comments.push((Letter::NAME_TYPE, name));
        }
        comments.extend(
            self.comments
                .iter()
                .cloned()
                .map(|c| (Letter::COMMENT_TYPE, c)),
        );
        comments.extend(self.rle_comments.clone());
        comments
    }
}

impl std::str::FromStr for Document {
    type Err = ParseDocumentError;

    fn from_str(s: &str) -> Result<Document, ParseDocumentError> {
        Document::load_from_str(s, FormatChoice::Autodetect)
    }
}

impl From<Plaintext> for Document {
    fn from(value: Plaintext) -> Document {
        Document {
            name: value.name,
            comments: value.comments,
            rle_comments: Vec::new(),
            pattern: value.pattern,
        }
    }
}

impl From<Document> for Plaintext {
    fn from(value: Document) -> Plaintext {
        Plaintext {
            name: value.name,
            comments: value.comments,
            pattern: value.pattern,
        }
    }
}

impl From<Rle> for Document {
    fn from(rle: Rle) -> Document {
        let mut name = None;
        let mut comments = Vec::new();
        let mut rle_comments = Vec::new();
        for (ty, value) in rle.comments {
            if ty == Letter::NAME_TYPE && name.is_none() {
                name = Some(value);
            } else if ty == Letter::COMMENT_TYPE || ty == Letter::ALT_COMMENT_TYPE {
                comments.push(value);
            } else {
                rle_comments.push((ty, value));
            }
        }
        Document {
            name,
            comments,
            rle_comments,
            pattern: rle.pattern,
        }
    }
}

impl From<Document> for Rle {
    fn from(value: Document) -> Rle {
        Rle {
            comments: value.make_rle_comments(),
            pattern: value.pattern,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DisplayDocument<'a> {
    doc: &'a Document,
    format: Format,
}

impl fmt::Display for DisplayDocument<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.format {
            Format::Plaintext => {
                let ptref = PlaintextRef {
                    name: self.doc.name.as_ref(),
                    comments: &self.doc.comments,
                    pattern: &self.doc.pattern,
                };
                write!(f, "{ptref}")
            }
            Format::Rle => {
                let comments = self.doc.make_rle_comments();
                let rleref = RleRef {
                    comments: &comments,
                    pattern: &self.doc.pattern,
                };
                write!(f, "{rleref}")
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FormatChoice {
    Autodetect,
    Fixed(Format),
}

impl From<Format> for FormatChoice {
    fn from(value: Format) -> FormatChoice {
        FormatChoice::Fixed(value)
    }
}

#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum ParseDocumentError {
    #[error("failed to detect file format type")]
    AutodetectFailed,
    #[error("failed to parse document as plaintext format")]
    Plaintext(#[from] PlaintextError),
    #[error("failed to parse document as RLE format")]
    Rle(#[from] RleError),
}

#[derive(Debug, Error)]
pub enum ReadDocumentError {
    #[error("failed to detect file format type")]
    AutodetectFailed,
    #[error("error reading file")]
    Io(#[from] std::io::Error),
    #[error("failed to parse document as plaintext format")]
    Plaintext(#[from] PlaintextError),
    #[error("failed to parse document as RLE format")]
    Rle(#[from] RleError),
}

#[derive(Debug, Error)]
pub enum DumpDocumentError {
    #[error("failed to detect file format type")]
    AutodetectFailed,
    #[error("error writing to file")]
    Io(#[from] std::io::Error),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rle_comment_roundabout() {
        let doc = concat!(
            "#O Richard K. Guy, 1969\n",
            "#c Not discovered by Conway\n",
            "#N Glider\n",
            "#C https://conwaylife.com/wiki/Glider\n",
            "x = 7, y = 7\n",
            "2$3bo$4bo$2b3o!\n",
        )
        .parse::<Document>()
        .unwrap();
        assert_eq!(
            doc.display(Format::Rle).to_string(),
            concat!(
                "#N Glider\n",
                "#C Not discovered by Conway\n",
                "#C https://conwaylife.com/wiki/Glider\n",
                "#O Richard K. Guy, 1969\n",
                "x = 7, y = 7\n",
                "2$3bo$4bo$2b3o!\n",
            )
        );
    }
}
