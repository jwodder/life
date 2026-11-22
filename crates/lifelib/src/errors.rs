//! Error types
use thiserror::Error;

#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
#[error("invalid Edges string")]
pub struct ParseEdgesError;

#[derive(Clone, Copy, Debug, Eq, Error, PartialEq)]
#[error("newline character {0:?} is not allowed inside a line")]
pub struct ParseLineError(pub char);

#[derive(Clone, Debug, Eq, Error, PartialEq)]
#[error("{source}: {string:?}")]
pub struct LineFromStringError {
    pub source: ParseLineError,
    pub string: String,
}

#[cfg(feature = "image")]
#[cfg_attr(docsrs, doc(cfg(feature = "image")))]
#[derive(Clone, Copy, Debug, Eq, Error, PartialEq)]
pub enum RenderError {
    #[error("image dimensions too large")]
    TooLarge,
}
