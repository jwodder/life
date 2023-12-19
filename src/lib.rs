use std::ops::{Index, IndexMut};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Life {
    height: usize,
    width: usize,
    cells: Vec<bool>,
}

impl Life {
    /// # Panics
    ///
    /// Panics if ``width * height`` exceeds the maximum capacity of a [`Vec`].
    pub fn new(mut height: usize, mut width: usize) -> Life {
        if height == 0 || width == 0 {
            height = 0;
            width = 0;
        }
        let area = width
            .checked_mul(height)
            .expect("width * height for new Life exceeds usize::MAX");
        let cells = vec![false; area];
        Life {
            height,
            width,
            cells,
        }
    }

    pub fn height(&self) -> usize {
        self.height
    }

    pub fn width(&self) -> usize {
        self.width
    }

    fn get_index(&self, y: usize, x: usize) -> Option<usize> {
        if (0..self.height).contains(&y) && (0..self.width).contains(&x) {
            y.checked_mul(self.width).and_then(|yw| yw.checked_add(x))
        } else {
            None
        }
    }

    pub fn get(&self, y: usize, x: usize) -> Option<bool> {
        self.get_index(y, x).map(|i| self.cells[i])
    }

    pub fn get_mut(&mut self, y: usize, x: usize) -> Option<&mut bool> {
        self.get_index(y, x).map(|i| &mut self.cells[i])
    }

    pub fn iter_alive(&self) -> IterAlive<'_> {
        IterAlive::new(self)
    }
}

impl Index<(usize, usize)> for Life {
    type Output = bool;

    fn index(&self, (y, x): (usize, usize)) -> &bool {
        let i = self
            .get_index(y, x)
            .expect("(y, x) index should be in bounds for Life");
        &self.cells[i]
    }
}

impl IndexMut<(usize, usize)> for Life {
    fn index_mut(&mut self, (y, x): (usize, usize)) -> &mut bool {
        let i = self
            .get_index(y, x)
            .expect("(y, x) index should be in bounds for Life");
        &mut self.cells[i]
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IterAlive<'a> {
    y: usize,
    x: usize,
    i: usize,
    life: &'a Life,
}

impl<'a> IterAlive<'a> {
    fn new(life: &'a Life) -> IterAlive<'a> {
        IterAlive {
            y: 0,
            x: 0,
            i: 0,
            life,
        }
    }
}

impl Iterator for IterAlive<'_> {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<(usize, usize)> {
        while let Some(&b) = self.life.cells.get(self.i) {
            let old_y = self.y;
            let old_x = self.x;
            // These operations won't overflow, as none of x, y, i will get
            // past isize::MAX, the maximum capacity of a Vec.
            self.i += 1;
            self.x += 1;
            if self.x >= self.life.width {
                self.x = 0;
                self.y += 1;
            }
            if b {
                return Some((old_y, old_x));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.life.cells.len().saturating_sub(self.i)))
    }
}

impl std::iter::FusedIterator for IterAlive<'_> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_iter_alive() {
        // .#.
        // ..#
        // ###
        let mut life = Life::new(3, 3);
        life[(0, 1)] = true;
        life[(1, 2)] = true;
        life[(2, 0)] = true;
        life[(2, 1)] = true;
        life[(2, 2)] = true;
        let mut iter = life.iter_alive();
        assert_eq!(iter.size_hint(), (0, Some(9)));
        assert_eq!(iter.next(), Some((0, 1)));
        assert_eq!(iter.size_hint(), (0, Some(7)));
        assert_eq!(iter.next(), Some((1, 2)));
        assert_eq!(iter.size_hint(), (0, Some(3)));
        assert_eq!(iter.next(), Some((2, 0)));
        assert_eq!(iter.size_hint(), (0, Some(2)));
        assert_eq!(iter.next(), Some((2, 1)));
        assert_eq!(iter.size_hint(), (0, Some(1)));
        assert_eq!(iter.next(), Some((2, 2)));
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
    }
}
