#![cfg_attr(docsrs, feature(doc_cfg))]
mod bounds;
mod builders;
mod document;
pub mod formats;
pub mod image;
mod pattern;
mod state;
pub mod utilities;
pub use crate::bounds::*;
pub use crate::builders::*;
pub use crate::document::*;
pub use crate::pattern::*;
pub use crate::state::*;
use strum::{Display, EnumString};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Coords {
    pub y: isize,
    pub x: isize,
}

impl Coords {
    pub const ORIGIN: Coords = Coords { y: 0, x: 0 };

    pub fn new(y: isize, x: isize) -> Coords {
        Coords { y, x }
    }
}

impl From<(isize, isize)> for Coords {
    fn from((y, x): (isize, isize)) -> Coords {
        Coords::new(y, x)
    }
}

impl From<Coords> for (isize, isize) {
    fn from(coords: Coords) -> (isize, isize) {
        (coords.y, coords.x)
    }
}

#[derive(
    Copy, Clone, Debug, Default, Display, EnumString, Hash, Eq, Ord, PartialEq, PartialOrd,
)]
#[strum(ascii_case_insensitive, serialize_all = "lowercase")]
pub enum Edges {
    #[default]
    Dead,
    WrapX,
    WrapY,
    WrapXY,
    GrowX,
    GrowY,
    GrowXY,
}

impl Edges {
    fn wraps_x(&self) -> bool {
        matches!(self, Edges::WrapX | Edges::WrapXY)
    }

    fn wraps_y(&self) -> bool {
        matches!(self, Edges::WrapY | Edges::WrapXY)
    }

    fn grows_x(&self) -> bool {
        matches!(self, Edges::GrowX | Edges::GrowXY)
    }

    fn grows_y(&self) -> bool {
        matches!(self, Edges::GrowY | Edges::GrowXY)
    }
}

pub fn sync_bounds(patterns: &[Pattern]) -> Result<Vec<Pattern>, BoundsError> {
    let Some((p0, rest)) = patterns.split_first() else {
        return Ok(Vec::new());
    };
    let bounds = rest
        .iter()
        .try_fold(p0.bounds(), |b, p| b.try_union(p.bounds()))?;
    Ok(patterns.iter().map(|p| p.resize(bounds)).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case("dead", Some(Edges::Dead))]
    #[case("Dead", Some(Edges::Dead))]
    #[case("DEAD", Some(Edges::Dead))]
    #[case("wrapx", Some(Edges::WrapX))]
    #[case("Wrapx", Some(Edges::WrapX))]
    #[case("WrapX", Some(Edges::WrapX))]
    #[case("WRAPX", Some(Edges::WrapX))]
    #[case("wrap-x", None)]
    #[case("wrapy", Some(Edges::WrapY))]
    #[case("Wrapy", Some(Edges::WrapY))]
    #[case("WrapY", Some(Edges::WrapY))]
    #[case("WRAPY", Some(Edges::WrapY))]
    #[case("wrap-y", None)]
    #[case("wrapxy", Some(Edges::WrapXY))]
    #[case("Wrapxy", Some(Edges::WrapXY))]
    #[case("WrapXy", Some(Edges::WrapXY))]
    #[case("WrapxY", Some(Edges::WrapXY))]
    #[case("WrapXY", Some(Edges::WrapXY))]
    #[case("WRAPXY", Some(Edges::WrapXY))]
    #[case("wrap-xy", None)]
    #[case("wrap-x-y", None)]
    #[case("growx", Some(Edges::GrowX))]
    #[case("growy", Some(Edges::GrowY))]
    #[case("growxy", Some(Edges::GrowXY))]
    fn test_edges_from_str(#[case] s: &str, #[case] parsed: Option<Edges>) {
        assert_eq!(s.parse::<Edges>().ok(), parsed);
    }

    #[rstest]
    #[case(Edges::Dead, "dead")]
    #[case(Edges::WrapX, "wrapx")]
    #[case(Edges::WrapY, "wrapy")]
    #[case(Edges::WrapXY, "wrapxy")]
    #[case(Edges::GrowX, "growx")]
    #[case(Edges::GrowY, "growy")]
    #[case(Edges::GrowXY, "growxy")]
    fn test_display_edges(#[case] value: Edges, #[case] s: &str) {
        assert_eq!(value.to_string(), s);
    }

    #[rstest]
    #[case(Edges::Dead)]
    #[case(Edges::WrapX)]
    #[case(Edges::WrapY)]
    #[case(Edges::WrapXY)]
    #[case(Edges::GrowX)]
    #[case(Edges::GrowY)]
    #[case(Edges::GrowXY)]
    fn test_display_then_parse_edges(#[case] value: Edges) {
        assert_eq!(value.to_string().parse::<Edges>().unwrap(), value);
    }
}
