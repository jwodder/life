//! File formats for storing Game of Life patterns
mod plaintext;
mod rle;
mod util;
pub use self::plaintext::*;
pub use self::rle::*;
use self::util::ascii_lines;
use std::path::Path;
use strum::{Display, EnumIter, EnumString};

#[derive(
    Clone, Copy, Debug, Display, EnumIter, EnumString, Eq, Hash, Ord, PartialEq, PartialOrd,
)]
#[strum(ascii_case_insensitive, serialize_all = "lowercase")]
pub enum Format {
    #[strum(serialize = "plaintext", serialize = "cells")]
    Plaintext,
    Rle,
}

impl Format {
    /// Returns an iterator over all [`Format`] variants
    pub fn iter() -> FormatIter {
        // To avoid the need for users to import the trait
        <Format as strum::IntoEnumIterator>::iter()
    }

    pub fn extension(&self) -> &'static str {
        match self {
            Format::Plaintext => "cells",
            Format::Rle => "rle",
        }
    }

    pub fn has_extension(&self, ext: &str) -> bool {
        self.extension()
            .eq_ignore_ascii_case(ext.strip_prefix('.').unwrap_or(ext))
    }

    pub fn identify<P: AsRef<Path>>(path: P) -> Option<Format> {
        let ext = path.as_ref().extension()?.to_str()?;
        Format::iter().find(|f| f.has_extension(ext))
    }

    /// Try to automatically determine the format of a pattern document.
    ///
    /// Returns `None` if the document is not valid for any supported format.
    ///
    /// If `detect()` returns `Some(f)`, parsing as format `f` may still fail,
    /// but parsing as any supported format other than `f` will *definitely*
    /// fail.
    pub fn detect(doc: &str) -> Option<Format> {
        let mut got_space_line = false;
        for ln in ascii_lines(doc).filter(|ln| !ln.is_empty()) {
            if ln.chars().all(|c| c == ' ' || c == '\t') {
                got_space_line = true;
            } else if !got_space_line && ln.starts_with(['!', '.', 'O']) {
                return Some(Format::Plaintext);
            } else if ln.starts_with('#') || ln.trim_start_matches([' ', '\t']).starts_with('x') {
                return Some(Format::Rle);
            } else {
                return None;
            }
        }
        Some(Format::Plaintext)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case("", Some(Format::Plaintext))]
    #[case(".O.\n..O\nOOO\n", Some(Format::Plaintext))]
    #[case("\n.O.\n..O\nOOO\n", Some(Format::Plaintext))]
    #[case(" \n.O.\n..O\nOOO\n", None)]
    #[case(" .O.\n..O\nOOO\n", None)]
    #[case("!Name: Glider\n.O.\n..O\nOOO\n", Some(Format::Plaintext))]
    #[case("x = 3, y = 3\nbo$2bo$3o!\n", Some(Format::Rle))]
    #[case("#N Glider\nx = 3, y = 3\nbo$2bo$3o!\n", Some(Format::Rle))]
    #[case(" \nx = 3, y = 3\nbo$2bo$3o!\n", Some(Format::Rle))]
    #[case(" x = 3, y = 3\nbo$2bo$3o!\n", Some(Format::Rle))]
    #[case("bo$2bo$3o!\n", None)]
    fn detect(#[case] doc: &str, #[case] r: Option<Format>) {
        assert_eq!(Format::detect(doc), r);
    }
}
