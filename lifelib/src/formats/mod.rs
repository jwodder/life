//! File formats for storing Game of Life patterns
mod plaintext;
mod rle;
mod util;
pub use self::plaintext::*;
pub use self::rle::*;
