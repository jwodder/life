use crate::{Coords, utilities::IterCoords};
use std::ops::{BitAnd, BitOr, Range};
use thiserror::Error;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Bounds {
    pub(crate) upper_left: Coords,
    pub(crate) width: usize,
    pub(crate) height: usize,
}

impl Bounds {
    pub const ZERO: Bounds = Bounds {
        upper_left: Coords { y: 0, x: 0 },
        width: 0,
        height: 0,
    };

    /// # Panics
    ///
    /// Panics if either `width` or `height` exceeds [`isize::MAX`] or if
    /// `width * height` exceeds [`usize::MAX`]
    pub fn new(height: usize, width: usize) -> Bounds {
        Bounds::new_with_upper_left(height, width, Coords { y: 0, x: 0 })
    }

    pub fn try_new(height: usize, width: usize) -> Result<Bounds, BoundsError> {
        Bounds::try_new_with_upper_left(height, width, Coords { y: 0, x: 0 })
    }

    /// # Panics
    ///
    /// Panics if any of the following are true:
    ///
    /// - `width * height` exceeds [`usize::MAX`]
    /// - `upper_left.y + height` exceeds [`isize::MAX`]
    /// - `upper_left.x + width` exceeds [`isize::MAX`]
    pub fn new_with_upper_left(height: usize, width: usize, upper_left: Coords) -> Bounds {
        match Bounds::try_new_with_upper_left(height, width, upper_left) {
            Ok(b) => b,
            Err(e) => panic!("failed to construct Bounds: {e}"),
        }
    }

    pub fn try_new_with_upper_left(
        height: usize,
        width: usize,
        upper_left: Coords,
    ) -> Result<Bounds, BoundsError> {
        if height == 0 || width == 0 {
            Ok(Bounds::ZERO)
        } else if width.checked_mul(height).is_none() {
            Err(BoundsError::AreaOverflow)
        } else if upper_left.y.checked_add_unsigned(height).is_none() {
            Err(BoundsError::MaxYOverflow)
        } else if upper_left.x.checked_add_unsigned(width).is_none() {
            Err(BoundsError::MaxXOverflow)
        } else {
            Ok(Bounds {
                height,
                width,
                upper_left,
            })
        }
    }

    pub fn is_empty(&self) -> bool {
        self.width == 0 || self.height == 0
    }

    pub fn contains<C: Into<Coords>>(&self, c: C) -> bool {
        let c = c.into();
        self.xrange().contains(&c.x) && self.yrange().contains(&c.y)
    }

    pub(crate) fn index<C: Into<Coords>>(&self, c: C) -> Option<usize> {
        let c = c.into();
        if self.contains(c) {
            let y = c.y.abs_diff(self.upper_left.y);
            let x = c.x.abs_diff(self.upper_left.x);
            y.checked_mul(self.width)?.checked_add(x)
        } else {
            None
        }
    }

    pub(crate) fn unindex(&self, i: usize) -> Option<Coords> {
        (i < (self.height * self.width)).then(|| {
            let y = self.upper_left.y.strict_add_unsigned(i / self.width);
            let x = self.upper_left.x.strict_add_unsigned(i % self.width);
            Coords { y, x }
        })
    }

    pub fn width(&self) -> usize {
        self.width
    }

    pub fn height(&self) -> usize {
        self.height
    }

    pub fn upper_left(&self) -> Coords {
        self.upper_left
    }

    pub(crate) fn yend(&self) -> isize {
        self.upper_left.y.strict_add_unsigned(self.height)
    }

    pub(crate) fn xend(&self) -> isize {
        self.upper_left.x.strict_add_unsigned(self.width)
    }

    // Note that this coordinate is *outside* the interior of the box
    pub fn lower_right(&self) -> Coords {
        Coords {
            y: self.yend(),
            x: self.xend(),
        }
    }

    pub fn yrange(&self) -> Range<isize> {
        self.upper_left.y..self.yend()
    }

    pub fn xrange(&self) -> Range<isize> {
        self.upper_left.x..self.xend()
    }

    pub fn moved_to<C: Into<Coords>>(&self, c: C) -> Result<Bounds, BoundsError> {
        Bounds::try_new_with_upper_left(self.height, self.width, c.into())
    }

    pub fn try_union(&self, other: Bounds) -> Result<Bounds, BoundsError> {
        if self.is_empty() {
            Ok(other)
        } else if other.is_empty() {
            Ok(*self)
        } else {
            let xstart = std::cmp::min(self.upper_left.x, other.upper_left.x);
            let ystart = std::cmp::min(self.upper_left.y, other.upper_left.y);
            let xend = std::cmp::max(self.xend(), other.xend());
            let yend = std::cmp::max(self.yend(), other.yend());
            if xstart >= xend || ystart >= yend {
                Ok(Bounds::ZERO)
            } else {
                let width = xstart.abs_diff(xend);
                let height = ystart.abs_diff(yend);
                Bounds::try_new_with_upper_left(
                    height,
                    width,
                    Coords {
                        y: ystart,
                        x: xstart,
                    },
                )
            }
        }
    }

    pub fn padded(&self, pad: Padding) -> Result<Bounds, PaddingError> {
        fn signed_add(left: usize, right: isize) -> Result<usize, PaddingError> {
            match left.checked_add_signed(right) {
                Some(v) => Ok(v),
                None if right < 0 => Ok(0),
                None => Err(PaddingError::Overflow),
            }
        }

        let y = self
            .upper_left
            .y
            .checked_sub(pad.top)
            .ok_or(PaddingError::Overflow)?;
        let x = self
            .upper_left
            .x
            .checked_sub(pad.left)
            .ok_or(PaddingError::Overflow)?;
        let height = signed_add(signed_add(self.height, pad.top)?, pad.bottom)?;
        let width = signed_add(signed_add(self.width, pad.left)?, pad.right)?;
        Bounds::try_new_with_upper_left(height, width, Coords { y, x }).map_err(Into::into)
    }
}

impl IntoIterator for Bounds {
    type Item = Coords;
    type IntoIter = IterCoords;

    fn into_iter(self) -> IterCoords {
        IterCoords::new(self)
    }
}

impl BitAnd for Bounds {
    type Output = Bounds;

    fn bitand(self, other: Bounds) -> Bounds {
        let xstart = std::cmp::max(self.upper_left.x, other.upper_left.x);
        let ystart = std::cmp::max(self.upper_left.y, other.upper_left.y);
        let xend = std::cmp::min(self.xend(), other.xend());
        let yend = std::cmp::min(self.yend(), other.yend());
        if xstart >= xend || ystart >= yend {
            Bounds::ZERO
        } else {
            let width = xstart.abs_diff(xend);
            let height = ystart.abs_diff(yend);
            Bounds {
                upper_left: Coords {
                    y: ystart,
                    x: xstart,
                },
                width,
                height,
            }
        }
    }
}

impl BitAnd<&Bounds> for Bounds {
    type Output = Bounds;

    fn bitand(self, other: &Bounds) -> Bounds {
        self & *other
    }
}

impl BitAnd<&Bounds> for &Bounds {
    type Output = Bounds;

    fn bitand(self, other: &Bounds) -> Bounds {
        *self & *other
    }
}

impl BitOr for Bounds {
    type Output = Bounds;

    fn bitor(self, other: Bounds) -> Bounds {
        match self.try_union(other) {
            Ok(b) => b,
            Err(e) => panic!("failed to construct Bounds: {e}"),
        }
    }
}

impl BitOr<&Bounds> for Bounds {
    type Output = Bounds;

    fn bitor(self, other: &Bounds) -> Bounds {
        self | *other
    }
}

impl BitOr<&Bounds> for &Bounds {
    type Output = Bounds;

    fn bitor(self, other: &Bounds) -> Bounds {
        *self | *other
    }
}

#[derive(Clone, Copy, Debug, Hash, Eq, Error, PartialEq)]
pub enum BoundsError {
    #[error("width * height exceeds usize::MAX")]
    AreaOverflow,
    #[error("y-coordinate upper bound exceeds isize::MAX")]
    MaxYOverflow,
    #[error("x-coordinate upper bound exceeds isize::MAX")]
    MaxXOverflow,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Padding {
    pub top: isize,
    pub bottom: isize,
    pub left: isize,
    pub right: isize,
}

impl Padding {
    pub const ZERO: Padding = Padding {
        top: 0,
        bottom: 0,
        left: 0,
        right: 0,
    };

    pub fn top(p: isize) -> Padding {
        Padding {
            top: p,
            ..Padding::default()
        }
    }

    pub fn bottom(p: isize) -> Padding {
        Padding {
            bottom: p,
            ..Padding::default()
        }
    }

    pub fn left(p: isize) -> Padding {
        Padding {
            left: p,
            ..Padding::default()
        }
    }

    pub fn right(p: isize) -> Padding {
        Padding {
            right: p,
            ..Padding::default()
        }
    }

    pub fn uniform(p: isize) -> Padding {
        Padding {
            top: p,
            bottom: p,
            left: p,
            right: p,
        }
    }

    pub fn horizontal(p: isize) -> Padding {
        Padding {
            left: p,
            right: p,
            ..Padding::default()
        }
    }

    pub fn vertical(p: isize) -> Padding {
        Padding {
            top: p,
            bottom: p,
            ..Padding::default()
        }
    }

    pub fn combine(self, other: Padding) -> Option<Padding> {
        Some(Padding {
            top: self.top.checked_add(other.top)?,
            bottom: self.bottom.checked_add(other.bottom)?,
            left: self.left.checked_add(other.left)?,
            right: self.right.checked_add(other.right)?,
        })
    }
}

#[derive(Clone, Copy, Debug, Hash, Eq, Error, PartialEq)]
pub enum PaddingError {
    #[error("adjusted dimensions overflowed")]
    Overflow,
    #[error("resulting bounds overflowed")]
    Bounds(#[from] BoundsError),
}

#[cfg(test)]
mod tests {
    use super::*;

    mod iter {
        use super::*;

        #[test]
        fn empty() {
            let bounds = Bounds::new(0, 0);
            let mut iter = bounds.into_iter();
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn three_by_two() {
            let bounds = Bounds::new(3, 2);
            let mut iter = bounds.into_iter();
            assert_eq!(iter.size_hint(), (6, Some(6)));
            assert_eq!(iter.next(), Some(Coords { y: 0, x: 0 }));
            assert_eq!(iter.size_hint(), (5, Some(5)));
            assert_eq!(iter.next(), Some(Coords { y: 0, x: 1 }));
            assert_eq!(iter.size_hint(), (4, Some(4)));
            assert_eq!(iter.next(), Some(Coords { y: 1, x: 0 }));
            assert_eq!(iter.size_hint(), (3, Some(3)));
            assert_eq!(iter.next(), Some(Coords { y: 1, x: 1 }));
            assert_eq!(iter.size_hint(), (2, Some(2)));
            assert_eq!(iter.next(), Some(Coords { y: 2, x: 0 }));
            assert_eq!(iter.size_hint(), (1, Some(1)));
            assert_eq!(iter.next(), Some(Coords { y: 2, x: 1 }));
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
        }
    }

    mod union {
        use super::*;

        #[test]
        fn overlapping() {
            // .........
            // .#####...
            // .###XX##.
            // .###XX##.
            // ....####.
            // ....####.
            // .........
            let b1 = Bounds::new_with_upper_left(3, 5, Coords { y: 1, x: 1 });
            let b2 = Bounds::new_with_upper_left(4, 4, Coords { y: 2, x: 4 });
            let b3 = b1 | b2;
            assert_eq!(b3.width(), 7);
            assert_eq!(b3.height(), 5);
            assert_eq!(b3.upper_left(), Coords { y: 1, x: 1 });
            assert_eq!(b3.lower_right(), Coords { y: 6, x: 8 });
        }

        #[test]
        fn contained() {
            // .......
            // .#####.
            // .##XX#.
            // .##XX#.
            // .#####.
            // .......
            let b1 = Bounds::new_with_upper_left(4, 5, Coords { y: 1, x: 1 });
            let b2 = Bounds::new_with_upper_left(2, 2, Coords { y: 2, x: 3 });
            let b3 = b1 | b2;
            assert_eq!(b3, b1);
        }

        #[test]
        fn adjacent() {
            // .........
            // .###OOOO.
            // .###OOOO.
            // .........
            let b1 = Bounds::new_with_upper_left(2, 3, Coords { y: 1, x: 1 });
            let b2 = Bounds::new_with_upper_left(2, 4, Coords { y: 1, x: 4 });
            let b3 = b1 | b2;
            assert_eq!(b3.width(), 7);
            assert_eq!(b3.height(), 2);
            assert_eq!(b3.upper_left(), Coords { y: 1, x: 1 });
            assert_eq!(b3.lower_right(), Coords { y: 3, x: 8 });
        }

        #[test]
        fn non_overlapping() {
            // .............
            // .........###.
            // .........###.
            // .........###.
            // .............
            // .####........
            // .####........
            // .............
            let b1 = Bounds::new_with_upper_left(2, 4, Coords { y: 5, x: 1 });
            let b2 = Bounds::new_with_upper_left(3, 3, Coords { y: 1, x: 9 });
            let b3 = b1 | b2;
            assert_eq!(b3.width(), 11);
            assert_eq!(b3.height(), 6);
            assert_eq!(b3.upper_left(), Coords { y: 1, x: 1 });
            assert_eq!(b3.lower_right(), Coords { y: 7, x: 12 });
        }

        #[test]
        fn empty_and_nonempty() {
            let b1 = Bounds::new_with_upper_left(2, 4, Coords { y: 5, x: 1 });
            let b2 = Bounds::ZERO;
            let b3 = b1 | b2;
            assert!(!b3.is_empty());
            assert_eq!(b3, b1);
        }

        #[test]
        fn empty_and_empty() {
            let b1 = Bounds::ZERO;
            let b2 = Bounds::ZERO;
            let b3 = b1 | b2;
            assert!(b3.is_empty());
            assert_eq!(b3, Bounds::ZERO);
        }

        #[cfg(target_pointer_width = "64")]
        #[test]
        #[should_panic(expected = "failed to construct Bounds: width * height exceeds usize::MAX")]
        fn area_overflow() {
            let b1 = Bounds::new_with_upper_left(1 << 32, 5, Coords { y: 2, x: 2 });
            let b2 = Bounds::new_with_upper_left(
                5,
                1 << 32,
                Coords {
                    y: 2,
                    x: -(1 << 32) - 2,
                },
            );
            let _ = b1 | b2;
        }
    }

    mod intersection {
        use super::*;

        #[test]
        fn overlapping() {
            // .........
            // .#####...
            // .###XX##.
            // .###XX##.
            // ....####.
            // ....####.
            // .........
            let b1 = Bounds::new_with_upper_left(3, 5, Coords { y: 1, x: 1 });
            let b2 = Bounds::new_with_upper_left(4, 4, Coords { y: 2, x: 4 });
            let b3 = b1 & b2;
            assert_eq!(b3.width(), 2);
            assert_eq!(b3.height(), 2);
            assert_eq!(b3.upper_left(), Coords { y: 2, x: 4 });
            assert_eq!(b3.lower_right(), Coords { y: 4, x: 6 });
        }

        #[test]
        fn contained() {
            // .......
            // .#####.
            // .##XX#.
            // .##XX#.
            // .#####.
            // .......
            let b1 = Bounds::new_with_upper_left(4, 5, Coords { y: 1, x: 1 });
            let b2 = Bounds::new_with_upper_left(2, 2, Coords { y: 2, x: 3 });
            let b3 = b1 & b2;
            assert_eq!(b3, b2);
        }

        #[test]
        fn adjacent() {
            // .........
            // .###OOOO.
            // .###OOOO.
            // .........
            let b1 = Bounds::new_with_upper_left(2, 3, Coords { y: 1, x: 1 });
            let b2 = Bounds::new_with_upper_left(2, 4, Coords { y: 1, x: 4 });
            let b3 = b1 & b2;
            assert!(b3.is_empty());
            assert_eq!(b3, Bounds::ZERO);
        }

        #[test]
        fn non_overlapping() {
            // .............
            // .........###.
            // .........###.
            // .........###.
            // .............
            // .####........
            // .####........
            // .............
            let b1 = Bounds::new_with_upper_left(2, 4, Coords { y: 5, x: 1 });
            let b2 = Bounds::new_with_upper_left(3, 3, Coords { y: 1, x: 9 });
            let b3 = b1 & b2;
            assert!(b3.is_empty());
            assert_eq!(b3, Bounds::ZERO);
        }

        #[test]
        fn empty_and_nonempty() {
            let b1 = Bounds::new_with_upper_left(2, 4, Coords { y: 5, x: 1 });
            let b2 = Bounds::ZERO;
            let b3 = b1 & b2;
            assert!(b3.is_empty());
            assert_eq!(b3, Bounds::ZERO);
        }

        #[test]
        fn empty_and_empty() {
            let b1 = Bounds::ZERO;
            let b2 = Bounds::ZERO;
            let b3 = b1 & b2;
            assert!(b3.is_empty());
            assert_eq!(b3, Bounds::ZERO);
        }
    }

    mod with_padding {
        use super::*;

        #[test]
        fn zero() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::ZERO;
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2, b);
        }

        #[test]
        fn top() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::top(3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 8);
            assert_eq!(b2.width(), 7);
            assert_eq!(b2.upper_left(), Coords { y: -1, x: 1 });
        }

        #[test]
        fn negative_top() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::top(-3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 2);
            assert_eq!(b2.width(), 7);
            assert_eq!(b2.upper_left(), Coords { y: 5, x: 1 });
        }

        #[test]
        fn bottom() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::bottom(3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 8);
            assert_eq!(b2.width(), 7);
            assert_eq!(b2.upper_left(), Coords { y: 2, x: 1 });
        }

        #[test]
        fn negative_bottom() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::bottom(-3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 2);
            assert_eq!(b2.width(), 7);
            assert_eq!(b2.upper_left(), Coords { y: 2, x: 1 });
        }

        #[test]
        fn vertical() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::vertical(3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 11);
            assert_eq!(b2.width(), 7);
            assert_eq!(b2.upper_left(), Coords { y: -1, x: 1 });
        }

        #[test]
        fn left() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::left(3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 5);
            assert_eq!(b2.width(), 10);
            assert_eq!(b2.upper_left(), Coords { y: 2, x: -2 });
        }

        #[test]
        fn negative_left() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::left(-3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 5);
            assert_eq!(b2.width(), 4);
            assert_eq!(b2.upper_left(), Coords { y: 2, x: 4 });
        }

        #[test]
        fn right() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::right(3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 5);
            assert_eq!(b2.width(), 10);
            assert_eq!(b2.upper_left(), Coords { y: 2, x: 1 });
        }

        #[test]
        fn negative_right() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::right(-3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 5);
            assert_eq!(b2.width(), 4);
            assert_eq!(b2.upper_left(), Coords { y: 2, x: 1 });
        }

        #[test]
        fn horizontal() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::horizontal(3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 5);
            assert_eq!(b2.width(), 13);
            assert_eq!(b2.upper_left(), Coords { y: 2, x: -2 });
        }

        #[test]
        fn uniform() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::uniform(3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2.height(), 11);
            assert_eq!(b2.width(), 13);
            assert_eq!(b2.upper_left(), Coords { y: -1, x: -2 });
        }

        #[test]
        fn negative_uniform_to_empty() {
            let b = Bounds::new_with_upper_left(5, 7, Coords { y: 2, x: 1 });
            let p = Padding::uniform(-3);
            let b2 = b.padded(p).unwrap();
            assert_eq!(b2, Bounds::ZERO);
        }

        #[test]
        fn combine_top_and_left() {
            let p1 = Padding::top(23);
            let p2 = Padding::left(17);
            let p3 = p1.combine(p2).unwrap();
            assert_eq!(
                p3,
                Padding {
                    top: 23,
                    left: 17,
                    ..Padding::default()
                }
            );
        }

        #[test]
        fn combine_top_and_top() {
            let p1 = Padding::top(23);
            let p2 = Padding::top(17);
            let p3 = p1.combine(p2).unwrap();
            assert_eq!(
                p3,
                Padding {
                    top: 40,
                    ..Padding::default()
                }
            );
        }

        #[test]
        fn combine_top_and_negative_top() {
            let p1 = Padding::top(23);
            let p2 = Padding::top(-17);
            let p3 = p1.combine(p2).unwrap();
            assert_eq!(
                p3,
                Padding {
                    top: 6,
                    ..Padding::default()
                }
            );
        }
    }
}
