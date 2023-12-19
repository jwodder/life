use std::fmt::{self, Write};
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

    pub fn enumerate(&self) -> Enumerate<'_> {
        Enumerate::new(self)
    }

    pub fn iter_alive(&self) -> IterAlive<'_> {
        IterAlive::new(self)
    }

    pub fn draw(&self, dead: char, alive: char) -> Draw<'_> {
        Draw::new(self, dead, alive)
    }

    pub fn advance(&self) -> Life {
        let mut next_state = self.clone();
        for y in 0..self.height {
            let yrange = range_about(y, self.height);
            for x in 0..self.width {
                let mut live_neighbors = 0;
                for x2 in range_about(x, self.width) {
                    for &y2 in &yrange {
                        if (y2, x2) != (y, x) && self[(y2, x2)] {
                            live_neighbors += 1;
                        }
                    }
                }
                match (live_neighbors, self[(y, x)]) {
                    (2 | 3, true) => (),                     // Remain alive
                    (3, false) => next_state[(y, x)] = true, // Be born
                    (_, true) => next_state[(y, x)] = false, // Die
                    (_, false) => (),                        // Stay dead
                }
            }
        }
        next_state
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
pub struct Enumerate<'a> {
    y: usize,
    x: usize,
    i: usize,
    life: &'a Life,
}

impl<'a> Enumerate<'a> {
    fn new(life: &'a Life) -> Enumerate<'a> {
        Enumerate {
            y: 0,
            x: 0,
            i: 0,
            life,
        }
    }
}

impl Iterator for Enumerate<'_> {
    type Item = ((usize, usize), bool);

    fn next(&mut self) -> Option<((usize, usize), bool)> {
        let &b = self.life.cells.get(self.i)?;
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
        Some(((old_y, old_x), b))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let left = self.life.cells.len().saturating_sub(self.i);
        (left, Some(left))
    }
}

impl ExactSizeIterator for Enumerate<'_> {}

impl std::iter::FusedIterator for Enumerate<'_> {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IterAlive<'a> {
    inner: Enumerate<'a>,
}

impl<'a> IterAlive<'a> {
    fn new(life: &'a Life) -> IterAlive<'a> {
        IterAlive {
            inner: Enumerate::new(life),
        }
    }
}

impl Iterator for IterAlive<'_> {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<(usize, usize)> {
        for (yx, b) in self.inner.by_ref() {
            if b {
                return Some(yx);
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.inner.size_hint();
        (0, upper)
    }
}

impl std::iter::FusedIterator for IterAlive<'_> {}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Draw<'a> {
    life: &'a Life,
    dead: char,
    alive: char,
}

impl<'a> Draw<'a> {
    fn new(life: &'a Life, dead: char, alive: char) -> Draw<'a> {
        Draw { life, dead, alive }
    }
}

impl fmt::Display for Draw<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for ((y, x), b) in self.life.enumerate() {
            if x == 0 && y > 0 {
                f.write_char('\n')?;
            }
            f.write_char(if b { self.alive } else { self.dead })?;
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum CellParser<'a> {
    DeadChars(&'a str),
    AliveChars(&'a str),
}

impl CellParser<'_> {
    fn parse(&self, c: char) -> bool {
        match self {
            CellParser::DeadChars(s) => !s.contains(c),
            CellParser::AliveChars(s) => s.contains(c),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct LifeParser<'a> {
    cell_parser: CellParser<'a>,
    min_width: usize,
    min_height: usize,
    max_width: Option<usize>,
    max_height: Option<usize>,
}

impl<'a> LifeParser<'a> {
    pub fn alive_chars(s: &'a str) -> LifeParser<'a> {
        LifeParser {
            cell_parser: CellParser::AliveChars(s),
            min_width: 0,
            min_height: 0,
            max_width: None,
            max_height: None,
        }
    }

    pub fn dead_chars(s: &'a str) -> LifeParser<'a> {
        LifeParser {
            cell_parser: CellParser::DeadChars(s),
            min_width: 0,
            min_height: 0,
            max_width: None,
            max_height: None,
        }
    }

    pub fn min_width(mut self, width: usize) -> Self {
        self.min_width = width;
        self
    }

    pub fn min_height(mut self, height: usize) -> Self {
        self.min_height = height;
        self
    }

    pub fn max_width(mut self, width: usize) -> Self {
        self.max_width = Some(width);
        self
    }

    pub fn max_height(mut self, height: usize) -> Self {
        self.max_height = Some(height);
        self
    }

    pub fn parse(&self, s: &str) -> Life {
        let mut live_points = Vec::new();
        let mut width = self.min_width;
        let mut height = self.min_height;
        for (y, line) in s.lines().enumerate() {
            if self.max_height.is_some_and(|h| y >= h) {
                break;
            }
            if y >= height {
                height = y + 1;
            }
            for (x, ch) in line.chars().enumerate() {
                if self.max_width.is_some_and(|w| x >= w) {
                    break;
                }
                if x >= width {
                    width = x + 1;
                }
                if self.cell_parser.parse(ch) {
                    live_points.push((y, x));
                }
            }
        }
        let mut life = Life::new(height, width);
        for yx in live_points {
            life[yx] = true;
        }
        life
    }
}

fn range_about(i: usize, limit: usize) -> Vec<usize> {
    let mut vals = Vec::with_capacity(3);
    if let Some(a) = i.checked_sub(1) {
        vals.push(a);
    }
    vals.push(i);
    if let Some(b) = i.checked_add(1) {
        if b < limit {
            vals.push(b);
        }
    }
    vals
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_enumerate() {
        // .#.
        // ..#
        // ###
        let mut life = Life::new(3, 3);
        life[(0, 1)] = true;
        life[(1, 2)] = true;
        life[(2, 0)] = true;
        life[(2, 1)] = true;
        life[(2, 2)] = true;
        let mut iter = life.enumerate();
        assert_eq!(iter.size_hint(), (9, Some(9)));
        assert_eq!(iter.next(), Some(((0, 0), false)));
        assert_eq!(iter.size_hint(), (8, Some(8)));
        assert_eq!(iter.next(), Some(((0, 1), true)));
        assert_eq!(iter.size_hint(), (7, Some(7)));
        assert_eq!(iter.next(), Some(((0, 2), false)));
        assert_eq!(iter.size_hint(), (6, Some(6)));
        assert_eq!(iter.next(), Some(((1, 0), false)));
        assert_eq!(iter.size_hint(), (5, Some(5)));
        assert_eq!(iter.next(), Some(((1, 1), false)));
        assert_eq!(iter.size_hint(), (4, Some(4)));
        assert_eq!(iter.next(), Some(((1, 2), true)));
        assert_eq!(iter.size_hint(), (3, Some(3)));
        assert_eq!(iter.next(), Some(((2, 0), true)));
        assert_eq!(iter.size_hint(), (2, Some(2)));
        assert_eq!(iter.next(), Some(((2, 1), true)));
        assert_eq!(iter.size_hint(), (1, Some(1)));
        assert_eq!(iter.next(), Some(((2, 2), true)));
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
    }

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

    #[test]
    fn test_draw() {
        // .#.
        // ..#
        // ###
        let mut life = Life::new(3, 3);
        life[(0, 1)] = true;
        life[(1, 2)] = true;
        life[(2, 0)] = true;
        life[(2, 1)] = true;
        life[(2, 2)] = true;
        assert_eq!(life.draw('.', '#').to_string(), ".#.\n..#\n###");
    }

    #[test]
    fn test_advance1() {
        // .#.
        // ..#
        // ###
        let mut life = Life::new(3, 3);
        life[(0, 1)] = true;
        life[(1, 2)] = true;
        life[(2, 0)] = true;
        life[(2, 1)] = true;
        life[(2, 2)] = true;
        let life2 = life.advance();
        assert_eq!(life2.draw('.', '#').to_string(), "...\n#.#\n.##");
    }

    #[test]
    fn test_advance2() {
        let mut life = Life::new(5, 5);
        life[(1, 2)] = true;
        life[(2, 3)] = true;
        life[(3, 1)] = true;
        life[(3, 2)] = true;
        life[(3, 3)] = true;
        let life2 = life.advance();
        assert_eq!(
            life2.draw('.', '#').to_string(),
            ".....\n.....\n.#.#.\n..##.\n..#.."
        );
    }

    #[test]
    fn test_parse1() {
        let parser = LifeParser::dead_chars(" .");
        let life = parser.parse(".#.\n..#\n###\n");
        assert_eq!(life.height(), 3);
        assert_eq!(life.width(), 3);
        assert_eq!(
            life.iter_alive().collect::<Vec<_>>(),
            [(0, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
        );
    }

    #[test]
    fn test_parse1_alive_chars() {
        let parser = LifeParser::alive_chars("+#");
        let life = parser.parse(".#.\n..#\n###\n");
        assert_eq!(life.height(), 3);
        assert_eq!(life.width(), 3);
        assert_eq!(
            life.iter_alive().collect::<Vec<_>>(),
            [(0, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
        );
    }

    #[test]
    fn test_parse2() {
        let parser = LifeParser::dead_chars(" .");
        let life = parser.parse(".....\n..#..\n...#.\n.###.\n.....");
        assert_eq!(life.height(), 5);
        assert_eq!(life.width(), 5);
        assert_eq!(
            life.iter_alive().collect::<Vec<_>>(),
            [(1, 2), (2, 3), (3, 1), (3, 2), (3, 3)]
        );
    }

    #[test]
    fn test_parse2_ragged() {
        let parser = LifeParser::dead_chars(" .");
        let life = parser.parse("\n..#\n...#\n.###\n");
        assert_eq!(life.height(), 4);
        assert_eq!(life.width(), 4);
        assert_eq!(
            life.iter_alive().collect::<Vec<_>>(),
            [(1, 2), (2, 3), (3, 1), (3, 2), (3, 3)]
        );
    }

    #[test]
    fn test_parse2_ragged_min_size() {
        let parser = LifeParser::dead_chars(" .").min_width(5).min_height(5);
        let life = parser.parse("\n..#\n...#\n.###\n");
        assert_eq!(life.height(), 5);
        assert_eq!(life.width(), 5);
        assert_eq!(
            life.iter_alive().collect::<Vec<_>>(),
            [(1, 2), (2, 3), (3, 1), (3, 2), (3, 3)]
        );
    }

    #[test]
    fn test_parse3() {
        let parser = LifeParser::dead_chars(" .")
            .min_width(5)
            .min_height(5)
            .max_height(5)
            .max_width(5);
        let life = parser.parse(" +\n   +\n++  +++\n");
        assert_eq!(life.height(), 5);
        assert_eq!(life.width(), 5);
        assert_eq!(
            life.iter_alive().collect::<Vec<_>>(),
            [(0, 1), (1, 3), (2, 0), (2, 1), (2, 4)],
        );
    }
}
