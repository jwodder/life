use std::fmt::{self, Write};
use std::ops::{Index, IndexMut};
use std::str::FromStr;
use thiserror::Error;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LifeState {
    height: usize,
    width: usize,
    edges: Edges,
    cells: Vec<bool>,
}

impl LifeState {
    /// # Panics
    ///
    /// Panics if ``width * height`` exceeds the maximum capacity of a [`Vec`].
    pub fn new(mut height: usize, mut width: usize, edges: Edges) -> LifeState {
        if height == 0 || width == 0 {
            height = 0;
            width = 0;
        }
        let area = width
            .checked_mul(height)
            .expect("width * height for new LifeState exceeds usize::MAX");
        let cells = vec![false; area];
        LifeState {
            height,
            width,
            edges,
            cells,
        }
    }

    pub fn height(&self) -> usize {
        self.height
    }

    pub fn width(&self) -> usize {
        self.width
    }

    pub fn edges(&self) -> Edges {
        self.edges
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

    pub fn advance(&self) -> LifeState {
        let mut next_state = self.clone();
        for y in 0..self.height {
            let yrange = self.edges.about_y(y, self.height);
            for x in 0..self.width {
                let mut live_neighbors = 0;
                for x2 in self.edges.about_x(x, self.width) {
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

impl Index<(usize, usize)> for LifeState {
    type Output = bool;

    fn index(&self, (y, x): (usize, usize)) -> &bool {
        let i = self
            .get_index(y, x)
            .expect("(y, x) index should be in bounds for LifeState");
        &self.cells[i]
    }
}

impl IndexMut<(usize, usize)> for LifeState {
    fn index_mut(&mut self, (y, x): (usize, usize)) -> &mut bool {
        let i = self
            .get_index(y, x)
            .expect("(y, x) index should be in bounds for LifeState");
        &mut self.cells[i]
    }
}

#[derive(Copy, Clone, Debug, Default, Hash, Eq, Ord, PartialEq, PartialOrd)]
pub enum Edges {
    #[default]
    Dead,
    WrapX,
    WrapY,
    WrapXY,
}

impl Edges {
    fn about_x(&self, x: usize, limit: usize) -> Vec<usize> {
        match self {
            Edges::Dead | Edges::WrapY => range_about(x, limit),
            Edges::WrapX | Edges::WrapXY => wrap_about(x, limit),
        }
    }

    fn about_y(&self, y: usize, limit: usize) -> Vec<usize> {
        match self {
            Edges::Dead | Edges::WrapX => range_about(y, limit),
            Edges::WrapY | Edges::WrapXY => wrap_about(y, limit),
        }
    }
}

impl FromStr for Edges {
    type Err = ParseEdgesError;

    fn from_str(s: &str) -> Result<Edges, ParseEdgesError> {
        if s.eq_ignore_ascii_case("dead") {
            Ok(Edges::Dead)
        } else if s.eq_ignore_ascii_case("wrapx") {
            Ok(Edges::WrapX)
        } else if s.eq_ignore_ascii_case("wrapy") {
            Ok(Edges::WrapY)
        } else if s.eq_ignore_ascii_case("wrapxy") {
            Ok(Edges::WrapXY)
        } else {
            Err(ParseEdgesError)
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
#[error("invalid Edges string")]
pub struct ParseEdgesError;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Enumerate<'a> {
    y: usize,
    x: usize,
    i: usize,
    life: &'a LifeState,
}

impl<'a> Enumerate<'a> {
    fn new(life: &'a LifeState) -> Enumerate<'a> {
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
    fn new(life: &'a LifeState) -> IterAlive<'a> {
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
    life: &'a LifeState,
    dead: char,
    alive: char,
}

impl<'a> Draw<'a> {
    fn new(life: &'a LifeState, dead: char, alive: char) -> Draw<'a> {
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

/// Parser for Game of Life drawings.
///
/// [`LifeParser`] parses [`LifeState`] instances from Game of Life states
/// expressed as simple drawings, such as produced by [`LifeState::draw()`].
/// Construct a [`LifeParser`] with either
/// [`dead_chars()`][LifeParser::dead_chars] or
/// [`alive_chars()`][LifeParser::alive_chars], optionally set the minimum
/// and/or maximum dimensions for the output, and parse strings with
/// [`parse()`][LifeParser::parse].
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct LifeParser<'a> {
    cell_parser: CellParser<'a>,
    edges: Edges,
    min_width: usize,
    min_height: usize,
    max_width: Option<usize>,
    max_height: Option<usize>,
}

impl<'a> LifeParser<'a> {
    /// Create a [`LifeParser`] that treats the characters in `s` as denoting
    /// dead cells and treats all other non-newline characters as denoting
    /// alive cells.
    ///
    /// # Example
    ///
    /// ```
    /// use life::LifeParser;
    ///
    /// let parser = LifeParser::dead_chars(" .");
    /// let life = parser.parse(".#?\n..#\n###\n");
    /// assert!(!life[(0, 0)]);
    /// assert!(life[(0, 1)]);
    /// assert!(life[(0, 2)]);
    /// ```
    pub fn dead_chars(s: &'a str) -> LifeParser<'a> {
        LifeParser {
            cell_parser: CellParser::DeadChars(s),
            edges: Edges::default(),
            min_width: 0,
            min_height: 0,
            max_width: None,
            max_height: None,
        }
    }

    /// Create a [`LifeParser`] that treats the characters in `s` as denoting
    /// alive cells and treats all other non-newline characters as denoting
    /// dead cells.
    ///
    /// # Example
    ///
    /// ```
    /// use life::LifeParser;
    ///
    /// let parser = LifeParser::alive_chars("+#");
    /// let life = parser.parse(".#?\n..#\n###\n");
    /// assert!(!life[(0, 0)]);
    /// assert!(life[(0, 1)]);
    /// assert!(!life[(0, 2)]);
    /// ```
    pub fn alive_chars(s: &'a str) -> LifeParser<'a> {
        LifeParser {
            cell_parser: CellParser::AliveChars(s),
            edges: Edges::default(),
            min_width: 0,
            min_height: 0,
            max_width: None,
            max_height: None,
        }
    }

    pub fn edges(mut self, edges: Edges) -> Self {
        self.edges = edges;
        self
    }

    /// Set the minimum width of parsed [`LifeState`] instances.
    ///
    /// If the input to [`LifeParser::parse()`] contains any lines with fewer
    /// than `width` characters, such lines will be padded with dead cells on
    /// the right.
    pub fn min_width(mut self, width: usize) -> Self {
        self.min_width = width;
        self
    }

    /// Set the minimum height of parsed [`LifeState`] instances.
    ///
    /// If the input to [`LifeParser::parse()`] contains fewer than
    /// `height` lines, the output structure will be padded with rows of dead
    /// cells on the bottom.
    pub fn min_height(mut self, height: usize) -> Self {
        self.min_height = height;
        self
    }

    /// Set the maximum width of parsed [`LifeState`] instances.
    ///
    /// If the input to [`LifeParser::parse()`] contains any lines with more
    /// than `width` characters, characters after the first `width` will be
    /// ignored.
    pub fn max_width(mut self, width: usize) -> Self {
        self.max_width = Some(width);
        self
    }

    /// Set the maximum height of parsed [`LifeState`] instances.
    ///
    /// If the input to [`LifeParser::parse()`] contains more than
    /// `height` lines, lines after the first `height` will be ignored.
    pub fn max_height(mut self, height: usize) -> Self {
        self.max_height = Some(height);
        self
    }

    /// Parse a [`LifeState`] instance from a string.
    ///
    /// Each line of the input defines a row of the output, with the first line
    /// corresponding to row 0.  Each character of each line defines a cell in
    /// that row, with the first character of each line corresponding to column
    /// 0.
    ///
    /// The height of the output will be the number of lines in the input or
    /// the value passed to [`LifeParser::max_height()`] (if any), whichever is
    /// smaller.  The width of the output will be the character-width of the
    /// longest input line (stopping after `max_height` lines, if set) or the
    /// value passed to [`LifeParser::max_width()`] (if any), whichever is
    /// smaller.
    pub fn parse(&self, s: &str) -> LifeState {
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
        let mut life = LifeState::new(height, width, self.edges);
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

fn wrap_about(i: usize, limit: usize) -> Vec<usize> {
    let mut vals = Vec::with_capacity(3);
    debug_assert!(limit > 0, "limit should be > 0");
    vals.push(i.checked_sub(1).unwrap_or(limit - 1));
    vals.push(i);
    match i.checked_add(1) {
        Some(b) if b < limit => vals.push(b),
        _ => vals.push(0),
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
        let mut life = LifeState::new(3, 3, Edges::Dead);
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
        let mut life = LifeState::new(3, 3, Edges::Dead);
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
        let mut life = LifeState::new(3, 3, Edges::Dead);
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
        let mut life = LifeState::new(3, 3, Edges::Dead);
        life[(0, 1)] = true;
        life[(1, 2)] = true;
        life[(2, 0)] = true;
        life[(2, 1)] = true;
        life[(2, 2)] = true;
        let life2 = life.advance();
        assert_eq!(life2.draw('.', '#').to_string(), "...\n#.#\n.##");
    }

    #[test]
    fn test_advance1_wrapx() {
        // ..#..
        // +..#.
        // +###+
        let mut life = LifeState::new(3, 3, Edges::WrapX);
        life[(0, 1)] = true;
        life[(1, 2)] = true;
        life[(2, 0)] = true;
        life[(2, 1)] = true;
        life[(2, 2)] = true;
        let life2 = life.advance();
        assert_eq!(life2.draw('.', '#').to_string(), "...\n...\n###");
    }

    #[test]
    fn test_advance1_wrapy() {
        // +++
        // .#.
        // ..#
        // ###
        // .+.
        let mut life = LifeState::new(3, 3, Edges::WrapY);
        life[(0, 1)] = true;
        life[(1, 2)] = true;
        life[(2, 0)] = true;
        life[(2, 1)] = true;
        life[(2, 2)] = true;
        let life2 = life.advance();
        assert_eq!(life2.draw('.', '#').to_string(), "#..\n#.#\n#.#");
    }

    #[test]
    fn test_advance1_wrapxy() {
        // +++++
        // ..#..
        // +..#.
        // +###+
        // ..+..
        let mut life = LifeState::new(3, 3, Edges::WrapXY);
        life[(0, 1)] = true;
        life[(1, 2)] = true;
        life[(2, 0)] = true;
        life[(2, 1)] = true;
        life[(2, 2)] = true;
        let life2 = life.advance();
        assert_eq!(life2.draw('.', '#').to_string(), "...\n...\n...");
    }

    #[test]
    fn test_advance2() {
        let mut life = LifeState::new(5, 5, Edges::Dead);
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

    #[test]
    fn test_parse4() {
        let parser = LifeParser::dead_chars(" .").max_height(3);
        let life = parser.parse(" +\n   +\n++  +++\n+ + + + + + +\n");
        assert_eq!(life.height(), 3);
        assert_eq!(life.width(), 7);
        assert_eq!(
            life.iter_alive().collect::<Vec<_>>(),
            [(0, 1), (1, 3), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6)],
        );
    }
}
