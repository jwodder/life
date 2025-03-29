//! Error types
use crate::formats::{PlaintextError, RleError};
use thiserror::Error;

#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
#[error("invalid Edges string")]
pub struct ParseEdgesError;

#[derive(Debug, Error)]
pub enum FromFileError {
    #[error("path does not have a supported file extension")]
    InvalidExtension,
    #[error("failed to read file contents")]
    Read(#[from] std::io::Error),
    #[error("failed to parse plaintext")]
    ParsePlaintext(#[from] PlaintextError),
    #[error("failed to parse RLE")]
    ParseRle(#[from] RleError),
}

#[derive(Clone, Copy, Debug, Eq, Error, PartialEq)]
#[error("newline character {0:?} is not allowed inside a line")]
pub struct ParseLineError(pub char);

#[derive(Clone, Debug, Eq, Error, PartialEq)]
#[error("{source}: {string:?}")]
pub struct LineFromStringError {
    pub source: ParseLineError,
    pub string: String,
}
