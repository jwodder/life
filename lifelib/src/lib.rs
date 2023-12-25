#![cfg_attr(docsrs, feature(doc_cfg))]
pub mod errors;
pub mod formats;
#[cfg(feature = "image")]
pub mod image;
pub mod utilities;
use crate::errors::*;
use crate::formats::*;
use crate::utilities::*;
use std::fs::read_to_string;
use std::ops::{Index, IndexMut, Not};
use std::path::Path;
use std::str::FromStr;

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum State {
    #[default]
    Dead,
    Live,
}

impl State {
    pub fn is_live(self) -> bool {
        self == State::Live
    }

    pub fn toggle(&mut self) {
        *self = !*self;
    }
}

impl Not for State {
    type Output = State;

    fn not(self) -> State {
        match self {
            State::Dead => State::Live,
            State::Live => State::Dead,
        }
    }
}

impl Not for &State {
    type Output = State;

    fn not(self) -> State {
        !*self
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pattern {
    height: usize,
    width: usize,
    edges: Edges,
    cells: Vec<State>,
}

impl Pattern {
    /// # Panics
    ///
    /// Panics if ``width * height`` exceeds the maximum capacity of a [`Vec`].
    pub fn new(mut height: usize, mut width: usize) -> Pattern {
        if height == 0 || width == 0 {
            height = 0;
            width = 0;
        }
        let area = width
            .checked_mul(height)
            .expect("width * height for new Pattern exceeds usize::MAX");
        let cells = vec![State::Dead; area];
        Pattern {
            height,
            width,
            edges: Edges::default(),
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

    pub fn with_edges(mut self, edges: Edges) -> Pattern {
        self.edges = edges;
        self
    }

    pub fn has_coord(&self, y: usize, x: usize) -> bool {
        (0..self.height).contains(&y) && (0..self.width).contains(&x)
    }

    fn get_index(&self, y: usize, x: usize) -> Option<usize> {
        if self.has_coord(y, x) {
            y.checked_mul(self.width).and_then(|yw| yw.checked_add(x))
        } else {
            None
        }
    }

    pub fn get(&self, y: usize, x: usize) -> Option<State> {
        self.get_index(y, x).map(|i| self.cells[i])
    }

    pub fn get_mut(&mut self, y: usize, x: usize) -> Option<&mut State> {
        self.get_index(y, x).map(|i| &mut self.cells[i])
    }

    pub fn birth(&mut self, y: usize, x: usize) {
        if let Some(st) = self.get_mut(y, x) {
            *st = State::Live;
        }
    }

    pub fn kill(&mut self, y: usize, x: usize) {
        if let Some(st) = self.get_mut(y, x) {
            *st = State::Dead;
        }
    }

    pub fn toggle(&mut self, y: usize, x: usize) {
        if let Some(st) = self.get_mut(y, x) {
            st.toggle();
        }
    }

    /// Set `length` cells in a single row starting at `(y, x)` to `state`.
    ///
    /// If `(y, x)` is not within the bounds of the `Pattern`, nothing happens.
    ///
    /// At most `width - x` cells are set, even if `length` is larger.
    pub fn set_run(&mut self, y: usize, x: usize, length: usize, state: State) {
        if let Some(i) = self.get_index(y, x) {
            let length = length.min(self.width - x);
            self.cells[i..i.saturating_add(length)].fill(state);
        }
    }

    pub fn run_lengths(&self) -> RunLengths<'_> {
        RunLengths::new(self)
    }

    pub fn enumerate(&self) -> Enumerate<'_> {
        Enumerate::new(self)
    }

    pub fn iter_live(&self) -> IterLive<'_> {
        IterLive::new(self)
    }

    pub fn draw(&self, dead: char, live: char) -> Draw<'_> {
        Draw::new(self, dead, live)
    }

    pub fn step(&self) -> Pattern {
        let mut next_state = self.clone();
        for y in 0..self.height {
            let yrange = self.edges.about_y(y, self.height);
            for x in 0..self.width {
                let mut alive = 0;
                for x2 in self.edges.about_x(x, self.width) {
                    for &y2 in &yrange {
                        if self[(y2, x2)].is_live() {
                            alive += 1;
                        }
                    }
                }
                match alive {
                    3 => next_state.birth(y, x),
                    4 => (),
                    _ => next_state.kill(y, x),
                }
            }
        }
        next_state
    }

    pub fn into_generations(self) -> Generations {
        Generations(self)
    }

    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Pattern, FromFileError> {
        let path = path.as_ref();
        match path.extension().and_then(|s| s.to_str()) {
            Some("cells") => {
                let s = read_to_string(path)?;
                Ok(s.parse::<Plaintext>()?.into())
            }
            Some("rle") => {
                let s = read_to_string(path)?;
                Ok(s.parse::<Rle>()?.into())
            }
            _ => Err(FromFileError::InvalidExtension),
        }
    }
}

impl Index<(usize, usize)> for Pattern {
    type Output = State;

    fn index(&self, (y, x): (usize, usize)) -> &State {
        let i = self
            .get_index(y, x)
            .expect("(y, x) index should be in bounds for Pattern");
        &self.cells[i]
    }
}

impl IndexMut<(usize, usize)> for Pattern {
    fn index_mut(&mut self, (y, x): (usize, usize)) -> &mut State {
        let i = self
            .get_index(y, x)
            .expect("(y, x) index should be in bounds for Pattern");
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternBuilder {
    edges: Edges,
    height: usize,
    width: usize,
    max_height: usize,
    max_width: usize,
    live: Vec<(usize, usize)>,
}

impl PatternBuilder {
    pub fn new() -> PatternBuilder {
        PatternBuilder {
            edges: Edges::default(),
            height: 0,
            width: 0,
            max_height: usize::MAX,
            max_width: usize::MAX,
            live: Vec::new(),
        }
    }

    pub fn edges(mut self, edges: Edges) -> Self {
        self.edges = edges;
        self
    }

    pub fn min_height(mut self, height: usize) -> Self {
        self.height = height.max(self.height);
        self
    }

    pub fn min_width(mut self, width: usize) -> Self {
        self.width = width.max(self.width);
        self
    }

    pub fn max_height(mut self, height: usize) -> Self {
        self.max_height = height;
        self.live.retain(|&(y, _)| y < height);
        self
    }

    pub fn max_width(mut self, width: usize) -> Self {
        self.max_width = width;
        self.live.retain(|&(_, x)| x < width);
        self
    }

    pub fn push(&mut self, y: usize, x: usize) {
        if (0..self.max_height).contains(&y) && (0..self.max_width).contains(&x) {
            if y >= self.height {
                self.height = y + 1;
            }
            if x >= self.width {
                self.width = x + 1;
            }
            self.live.push((y, x));
        }
    }

    pub fn build(self) -> Pattern {
        let mut life = Pattern::new(self.height, self.width).with_edges(self.edges);
        for (y, x) in self.live {
            life.birth(y, x);
        }
        life
    }
}

impl Default for PatternBuilder {
    fn default() -> PatternBuilder {
        PatternBuilder::new()
    }
}

impl Extend<(usize, usize)> for PatternBuilder {
    fn extend<I: IntoIterator<Item = (usize, usize)>>(&mut self, iter: I) {
        for (y, x) in iter {
            self.push(y, x);
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum CellParser<'a> {
    DeadChars(&'a str),
    LiveChars(&'a str),
}

impl CellParser<'_> {
    fn parse(&self, c: char) -> State {
        let b = match self {
            CellParser::DeadChars(s) => !s.contains(c),
            CellParser::LiveChars(s) => s.contains(c),
        };
        if b {
            State::Live
        } else {
            State::Dead
        }
    }
}

/// Parser for Game of Life drawings.
///
/// [`PatternParser`] parses [`Pattern`] instances from Game of Life patterns
/// expressed as simple drawings, such as produced by [`Pattern::draw()`].
///
/// Construct a [`PatternParser`] with either [`PatternParser::dead_chars()`]
/// or [`PatternParser::live_chars()`], optionally set the minimum and/or
/// maximum dimensions for the output, and parse drawings with
/// [`PatternParser::parse()`].
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct PatternParser<'a> {
    cell_parser: CellParser<'a>,
    edges: Edges,
    min_height: usize,
    min_width: usize,
    max_height: usize,
    max_width: usize,
}

impl<'a> PatternParser<'a> {
    /// Create a [`PatternParser`] that treats the characters in `s` as
    /// denoting dead cells and treats all other non-newline characters as
    /// denoting live cells.
    ///
    /// # Example
    ///
    /// ```
    /// use lifelib::PatternParser;
    ///
    /// let parser = PatternParser::dead_chars(" .");
    /// let life = parser.parse(".#?\n..#\n###\n");
    /// assert!(!life[(0, 0)].is_live());
    /// assert!(life[(0, 1)].is_live());
    /// assert!(life[(0, 2)].is_live());
    /// ```
    pub fn dead_chars(s: &'a str) -> PatternParser<'a> {
        PatternParser {
            cell_parser: CellParser::DeadChars(s),
            edges: Edges::default(),
            min_height: 0,
            min_width: 0,
            max_height: usize::MAX,
            max_width: usize::MAX,
        }
    }

    /// Create a [`PatternParser`] that treats the characters in `s` as
    /// denoting live cells and treats all other non-newline characters as
    /// denoting dead cells.
    ///
    /// # Example
    ///
    /// ```
    /// use lifelib::PatternParser;
    ///
    /// let parser = PatternParser::live_chars("+#");
    /// let life = parser.parse(".#?\n..#\n###\n");
    /// assert!(!life[(0, 0)].is_live());
    /// assert!(life[(0, 1)].is_live());
    /// assert!(!life[(0, 2)].is_live());
    /// ```
    pub fn live_chars(s: &'a str) -> PatternParser<'a> {
        PatternParser {
            cell_parser: CellParser::LiveChars(s),
            edges: Edges::default(),
            min_height: 0,
            min_width: 0,
            max_height: usize::MAX,
            max_width: usize::MAX,
        }
    }

    pub fn edges(mut self, edges: Edges) -> Self {
        self.edges = edges;
        self
    }

    /// Set the minimum height of parsed [`Pattern`] instances.
    ///
    /// If the input to [`PatternParser::parse()`] contains fewer than `height`
    /// lines, the output structure will be padded with rows of dead cells on
    /// the bottom.
    pub fn min_height(mut self, height: usize) -> Self {
        self.min_height = height;
        self
    }

    /// Set the minimum width of parsed [`Pattern`] instances.
    ///
    /// If the input to [`PatternParser::parse()`] contains any lines with
    /// fewer than `width` characters, such lines will be padded with dead
    /// cells on the right.
    pub fn min_width(mut self, width: usize) -> Self {
        self.min_width = width;
        self
    }

    /// Set the maximum height of parsed [`Pattern`] instances.
    ///
    /// If the input to [`PatternParser::parse()`] contains more than `height`
    /// lines, lines after the first `height` will be ignored.
    pub fn max_height(mut self, height: usize) -> Self {
        self.max_height = height;
        self
    }

    /// Set the maximum width of parsed [`Pattern`] instances.
    ///
    /// If the input to [`PatternParser::parse()`] contains any lines with more
    /// than `width` characters, characters after the first `width` will be
    /// ignored.
    pub fn max_width(mut self, width: usize) -> Self {
        self.max_width = width;
        self
    }

    /// Parse a [`Pattern`] instance from a string.
    ///
    /// Each line of the input defines a row of the output, with the first line
    /// corresponding to row 0.  Each character of each line defines a cell in
    /// that row, with the first character of each line corresponding to column
    /// 0.
    ///
    /// The height of the output will be the number of lines in the input or
    /// the value passed to [`PatternParser::max_height()`] (if any), whichever
    /// is smaller.  The width of the output will be the character-width of the
    /// longest input line (stopping after `max_height` lines, if set) or the
    /// value passed to [`PatternParser::max_width()`] (if any), whichever is
    /// smaller.
    pub fn parse(&self, s: &str) -> Pattern {
        let mut builder = PatternBuilder::new()
            .edges(self.edges)
            .min_height(self.min_height)
            .min_width(self.min_width)
            .max_height(self.max_height)
            .max_width(self.max_width);
        for (y, line) in s.lines().enumerate().take(self.max_height) {
            // Ensure that trailing dead rows count towards the height:
            builder = builder.min_height(y + 1);
            for (x, ch) in line.chars().enumerate().take(self.max_width) {
                // Ensure that trailing dead cells count towards the width:
                builder = builder.min_width(x + 1);
                if self.cell_parser.parse(ch).is_live() {
                    builder.push(y, x);
                }
            }
        }
        builder.build()
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
    use rstest::rstest;

    #[test]
    fn test_enumerate() {
        // .#.
        // ..#
        // ###
        let mut life = Pattern::new(3, 3);
        life.birth(0, 1);
        life.birth(1, 2);
        life.birth(2, 0);
        life.birth(2, 1);
        life.birth(2, 2);
        let mut iter = life.enumerate();
        assert_eq!(iter.size_hint(), (9, Some(9)));
        assert_eq!(iter.next(), Some(((0, 0), State::Dead)));
        assert_eq!(iter.size_hint(), (8, Some(8)));
        assert_eq!(iter.next(), Some(((0, 1), State::Live)));
        assert_eq!(iter.size_hint(), (7, Some(7)));
        assert_eq!(iter.next(), Some(((0, 2), State::Dead)));
        assert_eq!(iter.size_hint(), (6, Some(6)));
        assert_eq!(iter.next(), Some(((1, 0), State::Dead)));
        assert_eq!(iter.size_hint(), (5, Some(5)));
        assert_eq!(iter.next(), Some(((1, 1), State::Dead)));
        assert_eq!(iter.size_hint(), (4, Some(4)));
        assert_eq!(iter.next(), Some(((1, 2), State::Live)));
        assert_eq!(iter.size_hint(), (3, Some(3)));
        assert_eq!(iter.next(), Some(((2, 0), State::Live)));
        assert_eq!(iter.size_hint(), (2, Some(2)));
        assert_eq!(iter.next(), Some(((2, 1), State::Live)));
        assert_eq!(iter.size_hint(), (1, Some(1)));
        assert_eq!(iter.next(), Some(((2, 2), State::Live)));
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_live() {
        // .#.
        // ..#
        // ###
        let mut life = Pattern::new(3, 3);
        life.birth(0, 1);
        life.birth(1, 2);
        life.birth(2, 0);
        life.birth(2, 1);
        life.birth(2, 2);
        let mut iter = life.iter_live();
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
        let mut life = Pattern::new(3, 3);
        life.birth(0, 1);
        life.birth(1, 2);
        life.birth(2, 0);
        life.birth(2, 1);
        life.birth(2, 2);
        assert_eq!(life.draw('.', '#').to_string(), ".#.\n..#\n###");
    }

    #[test]
    fn test_step1() {
        // .#.
        // ..#
        // ###
        let mut life = Pattern::new(3, 3);
        life.birth(0, 1);
        life.birth(1, 2);
        life.birth(2, 0);
        life.birth(2, 1);
        life.birth(2, 2);
        let life2 = life.step();
        assert_eq!(life2.draw('.', '#').to_string(), "...\n#.#\n.##");
    }

    #[test]
    fn test_step1_wrapx() {
        // ..#..
        // +..#.
        // +###+
        let mut life = Pattern::new(3, 3).with_edges(Edges::WrapX);
        life.birth(0, 1);
        life.birth(1, 2);
        life.birth(2, 0);
        life.birth(2, 1);
        life.birth(2, 2);
        let life2 = life.step();
        assert_eq!(life2.draw('.', '#').to_string(), "...\n...\n###");
    }

    #[test]
    fn test_step1_wrapy() {
        // +++
        // .#.
        // ..#
        // ###
        // .+.
        let mut life = Pattern::new(3, 3).with_edges(Edges::WrapY);
        life.birth(0, 1);
        life.birth(1, 2);
        life.birth(2, 0);
        life.birth(2, 1);
        life.birth(2, 2);
        let life2 = life.step();
        assert_eq!(life2.draw('.', '#').to_string(), "#..\n#.#\n#.#");
    }

    #[test]
    fn test_step1_wrapxy() {
        // +++++
        // ..#..
        // +..#.
        // +###+
        // ..+..
        let mut life = Pattern::new(3, 3).with_edges(Edges::WrapXY);
        life.birth(0, 1);
        life.birth(1, 2);
        life.birth(2, 0);
        life.birth(2, 1);
        life.birth(2, 2);
        let life2 = life.step();
        assert_eq!(life2.draw('.', '#').to_string(), "...\n...\n...");
    }

    #[test]
    fn test_step2() {
        let mut life = Pattern::new(5, 5);
        life.birth(1, 2);
        life.birth(2, 3);
        life.birth(3, 1);
        life.birth(3, 2);
        life.birth(3, 3);
        let life2 = life.step();
        assert_eq!(
            life2.draw('.', '#').to_string(),
            ".....\n.....\n.#.#.\n..##.\n..#.."
        );
    }

    #[rstest]
    #[case(Edges::Dead, ".")]
    #[case(Edges::WrapX, "#")]
    #[case(Edges::WrapY, "#")]
    #[case(Edges::WrapXY, ".")]
    fn test_step_dot(#[case] edges: Edges, #[case] after: &str) {
        let mut life = Pattern::new(1, 1).with_edges(edges);
        life.birth(0, 0);
        let life2 = life.step();
        assert_eq!(life2.draw('.', '#').to_string(), after);
    }

    #[rstest]
    #[case(Edges::Dead, "..")]
    #[case(Edges::WrapX, "..")]
    #[case(Edges::WrapY, "##")]
    #[case(Edges::WrapXY, "#.")]
    fn test_step_horiz_domino(#[case] edges: Edges, #[case] after: &str) {
        let mut life = Pattern::new(1, 2).with_edges(edges);
        life.birth(0, 0);
        let life2 = life.step();
        assert_eq!(life2.draw('.', '#').to_string(), after);
    }

    #[rstest]
    #[case(Edges::Dead, ".\n.")]
    #[case(Edges::WrapX, "#\n#")]
    #[case(Edges::WrapY, ".\n.")]
    #[case(Edges::WrapXY, "#\n.")]
    fn test_step_vert_domino(#[case] edges: Edges, #[case] after: &str) {
        let mut life = Pattern::new(2, 1).with_edges(edges);
        life.birth(0, 0);
        let life2 = life.step();
        assert_eq!(life2.draw('.', '#').to_string(), after);
    }

    #[rstest]
    #[case(Edges::Dead, "..\n..")]
    #[case(Edges::WrapX, "##\n##")]
    #[case(Edges::WrapY, "##\n##")]
    #[case(Edges::WrapXY, "..\n..")]
    fn test_step_square_diag(#[case] edges: Edges, #[case] after: &str) {
        let mut life = Pattern::new(2, 2).with_edges(edges);
        life.birth(0, 0);
        life.birth(1, 1);
        let life2 = life.step();
        assert_eq!(life2.draw('.', '#').to_string(), after);
    }

    #[test]
    fn test_parse1() {
        let parser = PatternParser::dead_chars(" .");
        let life = parser.parse(".#.\n..#\n###\n");
        assert_eq!(life.height(), 3);
        assert_eq!(life.width(), 3);
        assert_eq!(
            life.iter_live().collect::<Vec<_>>(),
            [(0, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
        );
    }

    #[test]
    fn test_parse1_live_chars() {
        let parser = PatternParser::live_chars("+#");
        let life = parser.parse(".#.\n..#\n###\n");
        assert_eq!(life.height(), 3);
        assert_eq!(life.width(), 3);
        assert_eq!(
            life.iter_live().collect::<Vec<_>>(),
            [(0, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
        );
    }

    #[test]
    fn test_parse2() {
        let parser = PatternParser::dead_chars(" .");
        let life = parser.parse(".....\n..#..\n...#.\n.###.\n.....");
        assert_eq!(life.height(), 5);
        assert_eq!(life.width(), 5);
        assert_eq!(
            life.iter_live().collect::<Vec<_>>(),
            [(1, 2), (2, 3), (3, 1), (3, 2), (3, 3)]
        );
    }

    #[test]
    fn test_parse2_ragged() {
        let parser = PatternParser::dead_chars(" .");
        let life = parser.parse("\n..#\n...#\n.###\n");
        assert_eq!(life.height(), 4);
        assert_eq!(life.width(), 4);
        assert_eq!(
            life.iter_live().collect::<Vec<_>>(),
            [(1, 2), (2, 3), (3, 1), (3, 2), (3, 3)]
        );
    }

    #[test]
    fn test_parse2_ragged_min_size() {
        let parser = PatternParser::dead_chars(" .").min_width(5).min_height(5);
        let life = parser.parse("\n..#\n...#\n.###\n");
        assert_eq!(life.height(), 5);
        assert_eq!(life.width(), 5);
        assert_eq!(
            life.iter_live().collect::<Vec<_>>(),
            [(1, 2), (2, 3), (3, 1), (3, 2), (3, 3)]
        );
    }

    #[test]
    fn test_parse3() {
        let parser = PatternParser::dead_chars(" .")
            .min_width(5)
            .min_height(5)
            .max_height(5)
            .max_width(5);
        let life = parser.parse(" +\n   +\n++  +++\n");
        assert_eq!(life.height(), 5);
        assert_eq!(life.width(), 5);
        assert_eq!(
            life.iter_live().collect::<Vec<_>>(),
            [(0, 1), (1, 3), (2, 0), (2, 1), (2, 4)],
        );
    }

    #[test]
    fn test_parse4() {
        let parser = PatternParser::dead_chars(" .").max_height(3);
        let life = parser.parse(" +\n   +\n++  +++\n+ + + + + + +\n");
        assert_eq!(life.height(), 3);
        assert_eq!(life.width(), 7);
        assert_eq!(
            life.iter_live().collect::<Vec<_>>(),
            [(0, 1), (1, 3), (2, 0), (2, 1), (2, 4), (2, 5), (2, 6)],
        );
    }

    #[test]
    #[rustfmt::skip]
    fn test_parse_middle_blank_line() {
        let parser = PatternParser::dead_chars(" .");
        let life = parser.parse(concat!(
            "...OO\n",
            "..O..O\n",
            "...OO\n",
            "\n",
            ".OOOO\n",
            "O....O\n",
            "OO..OO\n",
        ));
        assert_eq!(life.height(), 7);
        assert_eq!(life.width(), 6);
        assert_eq!(life.draw('.', 'O').to_string(), concat!(
            "...OO.\n",
            "..O..O\n",
            "...OO.\n",
            "......\n",
            ".OOOO.\n",
            "O....O\n",
            "OO..OO",
        ));
    }

    #[test]
    fn test_zero_size() {
        let life = Pattern::new(0, 0);
        assert_eq!(life.get(0, 0), None);
        assert_eq!(life.draw('.', '#').to_string(), "");
        assert_eq!(life.step(), life);
        assert_eq!(life.enumerate().collect::<Vec<_>>(), Vec::new());
        assert_eq!(life.iter_live().collect::<Vec<_>>(), Vec::new());
    }

    #[test]
    #[rustfmt::skip]
    fn test_into_generations() {
        let parser = PatternParser::dead_chars(" .");
        let life = parser.parse(concat!(
            "......\n",
            "..#...\n",
            "...#..\n",
            ".###..\n",
            "......\n",
            "......\n",
        ));
        let mut iter = life.into_generations();
        let life = iter.next().unwrap();
        assert_eq!(life.draw('.', '#').to_string(), concat!(
            "......\n",
            "..#...\n",
            "...#..\n",
            ".###..\n",
            "......\n",
            "......",
        ));
        let life = iter.next().unwrap();
        assert_eq!(life.draw('.', '#').to_string(), concat!(
            "......\n",
            "......\n",
            ".#.#..\n",
            "..##..\n",
            "..#...\n",
            "......",
        ));
        let life = iter.next().unwrap();
        assert_eq!(life.draw('.', '#').to_string(), concat!(
            "......\n",
            "......\n",
            "...#..\n",
            ".#.#..\n",
            "..##..\n",
            "......",
        ));
        let life = iter.next().unwrap();
        assert_eq!(life.draw('.', '#').to_string(), concat!(
            "......\n",
            "......\n",
            "..#...\n",
            "...##.\n",
            "..##..\n",
            "......",
        ));
        let life = iter.next().unwrap();
        assert_eq!(life.draw('.', '#').to_string(), concat!(
            "......\n",
            "......\n",
            "...#..\n",
            "....#.\n",
            "..###.\n",
            "......",
        ));
        let life = iter.next().unwrap();
        assert_eq!(life.draw('.', '#').to_string(), concat!(
            "......\n",
            "......\n",
            "......\n",
            "..#.#.\n",
            "...##.\n",
            "...#..",
        ));
    }

    #[test]
    fn test_empty_builder() {
        let builder = PatternBuilder::new();
        let life = builder.build();
        assert_eq!(life.height(), 0);
        assert_eq!(life.width(), 0);
        assert_eq!(life.draw('.', '#').to_string(), "");
    }

    #[test]
    fn test_empty_builder_min_height() {
        let builder = PatternBuilder::new().min_height(1);
        let life = builder.build();
        // The height is zero because the width was zero, so both dimensions
        // are zeroed.
        assert_eq!(life.height(), 0);
        assert_eq!(life.width(), 0);
        assert_eq!(life.draw('.', '#').to_string(), "");
    }

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
    fn test_edges_from_str(#[case] s: &str, #[case] parsed: Option<Edges>) {
        assert_eq!(s.parse::<Edges>().ok(), parsed);
    }
}
