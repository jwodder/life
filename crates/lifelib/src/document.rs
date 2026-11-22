use crate::Pattern;
use crate::formats::{Format, Letter, Plaintext, PlaintextError, Rle, RleError};
use crate::utilities::Line;
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

    /// The pattern itself
    pub pattern: Pattern,
}

impl Document {
    pub fn from_rle_lossy(rle: Rle) -> Document {
        let mut name = None;
        let mut comments = Vec::new();
        for (ty, value) in rle.comments {
            if ty == Letter::NAME_TYPE && name.is_none() {
                name = Some(value);
            } else if ty == Letter::COMMENT_TYPE || ty == Letter::ALT_COMMENT_TYPE {
                comments.push(value);
            }
        }
        Document {
            name,
            comments,
            pattern: rle.pattern,
        }
    }

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
            Format::Rle => Ok(Document::from_rle_lossy(s.parse::<Rle>()?)),
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
            Format::Rle => Ok(Document::from_rle_lossy(s.parse::<Rle>()?)),
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
}

impl From<Plaintext> for Document {
    fn from(value: Plaintext) -> Document {
        Document {
            name: value.name,
            comments: value.comments,
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

impl From<Document> for Rle {
    fn from(value: Document) -> Rle {
        let mut comments = Vec::with_capacity(
            value
                .comments
                .len()
                .saturating_add(usize::from(value.name.is_some())),
        );
        if let Some(name) = value.name {
            comments.push((Letter::NAME_TYPE, name));
        }
        comments.extend(
            value
                .comments
                .into_iter()
                .map(|c| (Letter::COMMENT_TYPE, c)),
        );
        Rle {
            comments,
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
            // TODO: Do this without cloning everything:
            Format::Plaintext => write!(f, "{}", Plaintext::from(self.doc.clone())),
            Format::Rle => write!(f, "{}", Rle::from(self.doc.clone())),
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
