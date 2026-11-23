#![cfg_attr(docsrs, feature(doc_cfg))]
pub mod document;
pub mod formats;
pub mod image;
pub mod utilities;
use crate::utilities::*;
use bit_vec::BitVec;
use std::ops::{BitAnd, BitOr, BitXor, Not, Range};
use strum::{Display, EnumString};

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum State {
    #[default]
    Dead,
    Live,
}

impl State {
    pub fn living(alive: bool) -> State {
        if alive { State::Live } else { State::Dead }
    }

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

impl BitAnd for State {
    type Output = State;

    fn bitand(self, other: State) -> State {
        match (self, other) {
            (State::Live, State::Live) => State::Live,
            _ => State::Dead,
        }
    }
}

impl BitAnd<&State> for State {
    type Output = State;

    fn bitand(self, other: &State) -> State {
        self & *other
    }
}

impl BitAnd<&State> for &State {
    type Output = State;

    fn bitand(self, other: &State) -> State {
        *self & *other
    }
}

impl BitOr for State {
    type Output = State;

    fn bitor(self, other: State) -> State {
        match (self, other) {
            (State::Dead, State::Dead) => State::Dead,
            _ => State::Live,
        }
    }
}

impl BitOr<&State> for State {
    type Output = State;

    fn bitor(self, other: &State) -> State {
        self | *other
    }
}

impl BitOr<&State> for &State {
    type Output = State;

    fn bitor(self, other: &State) -> State {
        *self | *other
    }
}

impl BitXor for State {
    type Output = State;

    fn bitxor(self, other: State) -> State {
        match (self, other) {
            (State::Dead, State::Dead) => State::Dead,
            (State::Dead, State::Live) => State::Live,
            (State::Live, State::Dead) => State::Live,
            (State::Live, State::Live) => State::Dead,
        }
    }
}

impl BitXor<&State> for State {
    type Output = State;

    fn bitxor(self, other: &State) -> State {
        self ^ *other
    }
}

impl BitXor<&State> for &State {
    type Output = State;

    fn bitxor(self, other: &State) -> State {
        *self ^ *other
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Coords {
    pub y: isize,
    pub x: isize,
}

impl Coords {
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

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Bounds {
    upper_left: Coords,
    width: usize,
    height: usize,
}

impl Bounds {
    pub fn new(height: usize, width: usize) -> Bounds {
        Bounds::new_with_upper_left(height, width, Coords { y: 0, x: 0 })
    }

    /// # Panics
    ///
    /// Panics if any of the following are true:
    ///
    /// - `width * height` exceeds [`usize::MAX`]
    /// - `upper_left.y + height` exceeds [`isize::MAX`]
    /// - `upper_left.x + width` exceeds [`isize::MAX`]
    pub fn new_with_upper_left(height: usize, width: usize, upper_left: Coords) -> Bounds {
        if height == 0 || width == 0 {
            return Bounds::empty();
        }
        assert!(
            width.checked_mul(height).is_some(),
            "width * height exceeds usize::MAX"
        );
        assert!(
            upper_left.y.checked_add_unsigned(height).is_some(),
            "maximum y-coordinate exceeds isize::MAX"
        );
        assert!(
            upper_left.x.checked_add_unsigned(width).is_some(),
            "maximum x-coordinate exceeds isize::MAX"
        );
        Bounds {
            height,
            width,
            upper_left,
        }
    }

    pub fn empty() -> Bounds {
        Bounds {
            upper_left: Coords { y: 0, x: 0 },
            width: 0,
            height: 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.width == 0 || self.height == 0
    }

    pub fn contains<C: Into<Coords>>(&self, c: C) -> bool {
        let c = c.into();
        self.xrange().contains(&c.x) && self.yrange().contains(&c.y)
    }

    fn index<C: Into<Coords>>(&self, c: C) -> Option<usize> {
        let c = c.into();
        if self.contains(c) {
            let y = c.y.abs_diff(self.upper_left.y);
            let x = c.x.abs_diff(self.upper_left.x);
            y.checked_mul(self.width)?.checked_add(x)
        } else {
            None
        }
    }

    fn unindex(&self, i: usize) -> Option<Coords> {
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

    fn yend(&self) -> isize {
        self.upper_left.y.strict_add_unsigned(self.height)
    }

    fn xend(&self) -> isize {
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
            Bounds::empty()
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
        if self.is_empty() {
            other
        } else if other.is_empty() {
            self
        } else {
            let xstart = std::cmp::min(self.upper_left.x, other.upper_left.x);
            let ystart = std::cmp::min(self.upper_left.y, other.upper_left.y);
            let xend = std::cmp::max(self.xend(), other.xend());
            let yend = std::cmp::max(self.yend(), other.yend());
            if xstart >= xend || ystart >= yend {
                Bounds::empty()
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pattern {
    bounds: Bounds,
    edges: Edges,
    cells: BitVec,
}

impl Pattern {
    /// # Panics
    ///
    /// Panics if either `width` or `height` exceeds [`isize::MAX`] or if
    /// `width * height` exceeds [`usize::MAX`]
    pub fn new(height: usize, width: usize) -> Pattern {
        let bounds = Bounds::new(height, width);
        let cells = BitVec::from_elem(height * width, false);
        Pattern {
            bounds,
            edges: Edges::default(),
            cells,
        }
    }

    pub fn bounds(&self) -> Bounds {
        self.bounds
    }

    pub fn height(&self) -> usize {
        self.bounds.height
    }

    pub fn width(&self) -> usize {
        self.bounds.width
    }

    pub fn upper_left(&self) -> Coords {
        self.bounds.upper_left
    }

    pub fn edges(&self) -> Edges {
        self.edges
    }

    pub fn with_edges(mut self, edges: Edges) -> Pattern {
        self.edges = edges;
        self
    }

    pub fn contains<C: Into<Coords>>(&self, c: C) -> bool {
        self.bounds.contains(c)
    }

    fn index<C: Into<Coords>>(&self, c: C) -> Option<usize> {
        self.bounds.index(c)
    }

    pub fn get<C: Into<Coords>>(&self, c: C) -> Option<State> {
        self.index(c).map(|i| State::living(self.cells[i]))
    }

    pub fn is_live<C: Into<Coords>>(&self, c: C) -> bool {
        self.get(c) == Some(State::Live)
    }

    pub fn birth<C: Into<Coords>>(&mut self, c: C) {
        if let Some(i) = self.index(c) {
            self.cells.set(i, true);
        }
    }

    pub fn kill<C: Into<Coords>>(&mut self, c: C) {
        if let Some(i) = self.index(c) {
            self.cells.set(i, false);
        }
    }

    pub fn toggle<C: Into<Coords>>(&mut self, c: C) {
        if let Some(i) = self.index(c)
            && let Some(mut b) = self.cells.get_mut(i)
        {
            *b = !*b;
        }
    }

    /// Set `length` cells in a single row starting at `c` to `state`.
    ///
    /// If `c` is not within the bounds of the `Pattern`, nothing happens.
    ///
    /// At most `width - c.x` cells are set, even if `length` is larger.
    pub fn set_run<C: Into<Coords>>(&mut self, c: C, mut length: usize, state: State) {
        let c = c.into();
        if let Some(i) = self.index(c) {
            if let Some(rowrem) = self.width().checked_sub_signed(c.x)
                && rowrem < length
            {
                length = rowrem;
            }
            for j in i..i.saturating_add(length) {
                self.cells.set(j, state.is_live());
            }
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

    pub fn iter_coords(&self) -> IterCoords {
        self.bounds.into_iter()
    }

    pub fn draw(&self, dead: char, live: char) -> Draw<'_> {
        Draw::new(self, dead, live)
    }

    /// # Panics
    ///
    /// Panics if [`Pattern::edges()`] is [`Edges::GrowX`], [`Edges::GrowY`],
    /// or [`Edges::GrowXY`] and growing the pattern by the necessary amount
    /// would cause a bounds overflow
    pub fn step(&self) -> Pattern {
        let mut next_state = self.clone();
        let yrange = grow_range(self.bounds.yrange(), self.edges.grows_y());
        let xrange = grow_range(self.bounds.xrange(), self.edges.grows_x());
        for y in yrange.clone() {
            let yrng = adjacent(yrange.clone(), y, self.edges.wraps_y());
            for x in xrange.clone() {
                let mut alive = 0;
                for x2 in adjacent(xrange.clone(), x, self.edges.wraps_x()) {
                    for &y2 in &yrng {
                        if self.is_live((y2, x2)) {
                            alive += 1;
                        }
                    }
                }
                let c = Coords { y, x };
                match alive {
                    3 => {
                        next_state.ensure_contains(c);
                        next_state.birth(c);
                    }
                    4 => (),
                    _ => next_state.kill(c),
                }
            }
        }
        next_state
    }

    fn ensure_contains<C: Into<Coords>>(&mut self, c: C) {
        let c = c.into();
        let top = greater_by(c.y, self.bounds.upper_left.y);
        let left = greater_by(c.x, self.bounds.upper_left.x);
        // TODO: Only panic when strictly necessary:
        let bottom = greater_by(self.bounds.yend().strict_sub(1), c.y);
        let right = greater_by(self.bounds.xend().strict_sub(1), c.x);
        if top > 0 || left > 0 || bottom > 0 || right > 0 {
            let new_ul = Coords {
                y: self.bounds.upper_left.y.strict_sub_unsigned(top),
                x: self.bounds.upper_left.x.strict_sub_unsigned(left),
            };
            let new_height = self.bounds.height.strict_add(top).strict_add(bottom);
            let new_width = self.bounds.width.strict_add(left).strict_add(right);
            let new_bounds = Bounds::new_with_upper_left(new_height, new_width, new_ul);
            *self = self.resize(new_bounds);
        }
    }

    pub fn into_generations(self) -> Generations {
        Generations(self)
    }

    pub fn population(&self) -> u64 {
        self.cells.count_ones()
    }

    pub fn resize(&self, bounds: Bounds) -> Pattern {
        let cells = BitVec::from_fn(bounds.height * bounds.width, |i| {
            bounds.unindex(i).is_some_and(|c| self.is_live(c))
        });
        Pattern {
            cells,
            bounds,
            edges: self.edges,
        }
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternBuilder {
    edges: Edges,
    height: usize,
    width: usize,
    max_height: usize,
    max_width: usize,
    live: Vec<Coords>,
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
        if let Ok(h) = isize::try_from(height) {
            self.live.retain(|c| c.y < h);
        }
        self
    }

    pub fn max_width(mut self, width: usize) -> Self {
        self.max_width = width;
        if let Ok(w) = isize::try_from(width) {
            self.live.retain(|c| c.x < w);
        }
        self
    }

    pub fn push<C: Into<Coords>>(&mut self, c: C) {
        let c = c.into();
        if let Ok(y) = usize::try_from(c.y)
            && let Ok(x) = usize::try_from(c.x)
            && (0..self.max_height).contains(&y)
            && (0..self.max_width).contains(&x)
        {
            if y >= self.height {
                self.height = y + 1;
            }
            if x >= self.width {
                self.width = x + 1;
            }
            self.live.push(c);
        }
    }

    pub fn build(self) -> Pattern {
        let mut pat = Pattern::new(self.height, self.width).with_edges(self.edges);
        for c in self.live {
            pat.birth(c);
        }
        pat
    }
}

impl Default for PatternBuilder {
    fn default() -> PatternBuilder {
        PatternBuilder::new()
    }
}

impl<C: Into<Coords>> Extend<C> for PatternBuilder {
    fn extend<I: IntoIterator<Item = C>>(&mut self, iter: I) {
        for c in iter {
            self.push(c);
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
        if b { State::Live } else { State::Dead }
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
    /// assert!(!life.is_live((0, 0)));
    /// assert!(life.is_live((0, 1)));
    /// assert!(life.is_live((0, 2)));
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
    /// assert!(!life.is_live((0, 0)));
    /// assert!(life.is_live((0, 1)));
    /// assert!(!life.is_live((0, 2)));
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
                // TODO: Return Err on large input?
                // TODO: Document behavior for large input
                if self.cell_parser.parse(ch).is_live()
                    && let Ok(yi) = isize::try_from(y)
                    && let Ok(xi) = isize::try_from(x)
                {
                    builder.push((yi, xi));
                }
            }
        }
        builder.build()
    }
}

fn adjacent(range: Range<isize>, i: isize, wrap: bool) -> Vec<isize> {
    let mut vals = Vec::with_capacity(3);
    let mut a = i.checked_sub(1).filter(|&a| a >= range.start);
    if a.is_none() && wrap {
        a = Some(range.end - 1);
    }
    if let Some(a) = a {
        vals.push(a);
    }
    vals.push(i);
    let mut b = i.checked_add(1).filter(|&b| b < range.end);
    if b.is_none() && wrap {
        b = Some(range.start);
    }
    if let Some(b) = b {
        vals.push(b);
    }
    vals
}

fn grow_range(mut range: Range<isize>, grow: bool) -> Range<isize> {
    if grow {
        // TODO: Handle numeric overflow
        range.start -= 1;
        range.end += 1;
    }
    range
}

fn greater_by(lesser: isize, greater: isize) -> usize {
    if lesser < greater {
        lesser.abs_diff(greater)
    } else {
        0
    }
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
        life.birth((0, 1));
        life.birth((1, 2));
        life.birth((2, 0));
        life.birth((2, 1));
        life.birth((2, 2));
        let mut iter = life.enumerate();
        assert_eq!(iter.size_hint(), (9, Some(9)));
        assert_eq!(iter.next(), Some((Coords { y: 0, x: 0 }, State::Dead)));
        assert_eq!(iter.size_hint(), (8, Some(8)));
        assert_eq!(iter.next(), Some((Coords { y: 0, x: 1 }, State::Live)));
        assert_eq!(iter.size_hint(), (7, Some(7)));
        assert_eq!(iter.next(), Some((Coords { y: 0, x: 2 }, State::Dead)));
        assert_eq!(iter.size_hint(), (6, Some(6)));
        assert_eq!(iter.next(), Some((Coords { y: 1, x: 0 }, State::Dead)));
        assert_eq!(iter.size_hint(), (5, Some(5)));
        assert_eq!(iter.next(), Some((Coords { y: 1, x: 1 }, State::Dead)));
        assert_eq!(iter.size_hint(), (4, Some(4)));
        assert_eq!(iter.next(), Some((Coords { y: 1, x: 2 }, State::Live)));
        assert_eq!(iter.size_hint(), (3, Some(3)));
        assert_eq!(iter.next(), Some((Coords { y: 2, x: 0 }, State::Live)));
        assert_eq!(iter.size_hint(), (2, Some(2)));
        assert_eq!(iter.next(), Some((Coords { y: 2, x: 1 }, State::Live)));
        assert_eq!(iter.size_hint(), (1, Some(1)));
        assert_eq!(iter.next(), Some((Coords { y: 2, x: 2 }, State::Live)));
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
        life.birth((0, 1));
        life.birth((1, 2));
        life.birth((2, 0));
        life.birth((2, 1));
        life.birth((2, 2));
        let mut iter = life.iter_live();
        assert_eq!(iter.size_hint(), (0, Some(9)));
        assert_eq!(iter.next(), Some(Coords { y: 0, x: 1 }));
        assert_eq!(iter.size_hint(), (0, Some(7)));
        assert_eq!(iter.next(), Some(Coords { y: 1, x: 2 }));
        assert_eq!(iter.size_hint(), (0, Some(3)));
        assert_eq!(iter.next(), Some(Coords { y: 2, x: 0 }));
        assert_eq!(iter.size_hint(), (0, Some(2)));
        assert_eq!(iter.next(), Some(Coords { y: 2, x: 1 }));
        assert_eq!(iter.size_hint(), (0, Some(1)));
        assert_eq!(iter.next(), Some(Coords { y: 2, x: 2 }));
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
        life.birth((0, 1));
        life.birth((1, 2));
        life.birth((2, 0));
        life.birth((2, 1));
        life.birth((2, 2));
        assert_eq!(life.draw('.', '#').to_string(), ".#.\n..#\n###");
    }

    mod step {
        use super::*;

        #[test]
        fn test_step1() {
            // .#.
            // ..#
            // ###
            let mut life = Pattern::new(3, 3);
            life.birth((0, 1));
            life.birth((1, 2));
            life.birth((2, 0));
            life.birth((2, 1));
            life.birth((2, 2));
            let life2 = life.step();
            assert_eq!(life2.draw('.', '#').to_string(), "...\n#.#\n.##");
        }

        #[test]
        fn test_step1_wrapx() {
            // ..#..
            // +..#.
            // +###+
            let mut life = Pattern::new(3, 3).with_edges(Edges::WrapX);
            life.birth((0, 1));
            life.birth((1, 2));
            life.birth((2, 0));
            life.birth((2, 1));
            life.birth((2, 2));
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
            life.birth((0, 1));
            life.birth((1, 2));
            life.birth((2, 0));
            life.birth((2, 1));
            life.birth((2, 2));
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
            life.birth((0, 1));
            life.birth((1, 2));
            life.birth((2, 0));
            life.birth((2, 1));
            life.birth((2, 2));
            let life2 = life.step();
            assert_eq!(life2.draw('.', '#').to_string(), "...\n...\n...");
        }

        #[test]
        fn test_step2() {
            let mut life = Pattern::new(5, 5);
            life.birth((1, 2));
            life.birth((2, 3));
            life.birth((3, 1));
            life.birth((3, 2));
            life.birth((3, 3));
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
            life.birth((0, 0));
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
            life.birth((0, 0));
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
            life.birth((0, 0));
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
            life.birth((0, 0));
            life.birth((1, 1));
            let life2 = life.step();
            assert_eq!(life2.draw('.', '#').to_string(), after);
        }

        #[test]
        fn grow_glider() {
            // .#.
            // ..#
            // ###
            let mut life = Pattern::new(3, 3).with_edges(Edges::GrowXY);
            life.birth((0, 1));
            life.birth((1, 2));
            life.birth((2, 0));
            life.birth((2, 1));
            life.birth((2, 2));
            let life2 = life.step();
            assert_eq!(life2.draw('.', '#').to_string(), "...\n#.#\n.##\n.#.");
            assert_eq!(life2.height(), 4);
            assert_eq!(life2.width(), 3);
            assert_eq!(life2.upper_left(), Coords { y: 0, x: 0 });
            let life3 = life2.step();
            assert_eq!(life3.draw('.', '#').to_string(), "...\n..#\n#.#\n.##");
            assert_eq!(life3.height(), 4);
            assert_eq!(life3.width(), 3);
            assert_eq!(life3.upper_left(), Coords { y: 0, x: 0 });
            let life4 = life3.step();
            assert_eq!(life4.draw('.', '#').to_string(), "....\n.#..\n..##\n.##.");
            assert_eq!(life4.height(), 4);
            assert_eq!(life4.width(), 4);
            assert_eq!(life4.upper_left(), Coords { y: 0, x: 0 });
            let life5 = life4.step();
            assert_eq!(life5.draw('.', '#').to_string(), "....\n..#.\n...#\n.###");
            assert_eq!(life5.height(), 4);
            assert_eq!(life5.width(), 4);
            assert_eq!(life5.upper_left(), Coords { y: 0, x: 0 });
        }

        #[test]
        fn grow_lightweight_spaceship() {
            // <https://conwaylife.com/wiki/Lightweight_spaceship>
            // .#..#
            // #....
            // #...#
            // ####.
            let mut life = Pattern::new(4, 5).with_edges(Edges::GrowXY);
            life.birth((0, 1));
            life.birth((0, 4));
            life.birth((1, 0));
            life.birth((2, 0));
            life.birth((2, 4));
            life.birth((3, 0));
            life.birth((3, 1));
            life.birth((3, 2));
            life.birth((3, 3));
            let life2 = life.step();
            assert_eq!(life2.height(), 5);
            assert_eq!(life2.width(), 6);
            assert_eq!(life2.upper_left(), Coords { y: 0, x: -1 });
            assert_eq!(
                life2.draw('.', '#').to_string(),
                "......\n.##...\n##.##.\n.####.\n..##.."
            );
            let life3 = life2.step();
            assert_eq!(life3.height(), 5);
            assert_eq!(life3.width(), 6);
            assert_eq!(life3.upper_left(), Coords { y: 0, x: -1 });
            assert_eq!(
                life3.draw('.', '#').to_string(),
                "......\n####..\n#...#.\n#.....\n.#..#."
            );
            let life4 = life3.step();
            assert_eq!(life4.height(), 5);
            assert_eq!(life4.width(), 7);
            assert_eq!(life4.upper_left(), Coords { y: 0, x: -2 });
            assert_eq!(
                life4.draw('.', '#').to_string(),
                "..##...\n.####..\n##.##..\n.##....\n......."
            );
            let life5 = life4.step();
            assert_eq!(life5.height(), 5);
            assert_eq!(life5.width(), 7);
            assert_eq!(life5.upper_left(), Coords { y: 0, x: -2 });
            assert_eq!(
                life5.draw('.', '#').to_string(),
                ".#..#..\n#......\n#...#..\n####...\n......."
            );
        }

        #[test]
        fn grow_crab() {
            // <https://conwaylife.com/wiki/Crab>
            let life = PatternParser::live_chars("#")
                .edges(Edges::GrowXY)
                .parse(concat!(
                    "........##...\n",
                    ".......##....\n",
                    ".........#...\n",
                    "...........##\n",
                    "..........#..\n",
                    ".............\n",
                    ".........#..#\n",
                    ".##.....##...\n",
                    "##.....#.....\n",
                    "..#....#.#...\n",
                    "....##..#....\n",
                    "....##.......\n",
                ));
            let life2 = life.step();
            assert_eq!(life2.height(), 12);
            assert_eq!(life2.width(), 13);
            assert_eq!(life2.upper_left(), Coords { y: 0, x: 0 });
            assert_eq!(
                life2.draw('.', '#').to_string(),
                concat!(
                    ".......###...\n",
                    ".......#.....\n",
                    "........#....\n",
                    "..........##.\n",
                    "...........#.\n",
                    ".............\n",
                    "........##...\n",
                    "###.....##...\n",
                    "#......#.#...\n",
                    ".#....##.....\n",
                    "...####.#....\n",
                    "....##.......",
                )
            );
            let life3 = life2.step();
            assert_eq!(life3.height(), 13);
            assert_eq!(life3.width(), 13);
            assert_eq!(life3.upper_left(), Coords { y: -1, x: 0 });
            assert_eq!(
                life3.draw('.', '#').to_string(),
                concat!(
                    "........#....\n",
                    ".......##....\n",
                    ".......#.#...\n",
                    ".............\n",
                    "..........##.\n",
                    "..........##.\n",
                    ".............\n",
                    ".#......##...\n",
                    "##.....#..#..\n",
                    "#.#...##.#...\n",
                    "....#........\n",
                    "...#.........\n",
                    "...#..#......",
                )
            );
            let life4 = life3.step();
            assert_eq!(life4.height(), 13);
            assert_eq!(life4.width(), 13);
            assert_eq!(life4.upper_left(), Coords { y: -1, x: 0 });
            assert_eq!(
                life4.draw('.', '#').to_string(),
                concat!(
                    ".......##....\n",
                    ".......#.#...\n",
                    ".......#.....\n",
                    "..........#..\n",
                    "..........##.\n",
                    "..........##.\n",
                    ".........##..\n",
                    "##......##...\n",
                    "#.#...##..#..\n",
                    "#.....###....\n",
                    "...#.........\n",
                    "...##........\n",
                    ".............",
                )
            );
            let life5 = life4.step();
            assert_eq!(life5.height(), 13);
            assert_eq!(life5.width(), 14);
            assert_eq!(life5.upper_left(), Coords { y: -1, x: -1 });
            assert_eq!(
                life5.draw('.', '#').to_string(),
                concat!(
                    "........##....\n",
                    ".......##.....\n",
                    ".........#....\n",
                    "...........##.\n",
                    "..........#...\n",
                    "..............\n",
                    ".........#..#.\n",
                    ".##.....##....\n",
                    "##.....#......\n",
                    "..#....#.#....\n",
                    "....##..#.....\n",
                    "....##........\n",
                    "..............",
                )
            );
            let life9 = life4.into_generations().nth(5).unwrap();
            assert_eq!(life9.height(), 14);
            assert_eq!(life9.width(), 15);
            assert_eq!(life9.upper_left(), Coords { y: -2, x: -2 });
            assert_eq!(
                life9.draw('.', '#').to_string(),
                concat!(
                    "........##.....\n",
                    ".......##......\n",
                    ".........#.....\n",
                    "...........##..\n",
                    "..........#....\n",
                    "...............\n",
                    ".........#..#..\n",
                    ".##.....##.....\n",
                    "##.....#.......\n",
                    "..#....#.#.....\n",
                    "....##..#......\n",
                    "....##.........\n",
                    "...............\n",
                    "...............",
                )
            );
        }
    }

    mod parse {
        use super::*;

        #[test]
        fn test_parse1() {
            let parser = PatternParser::dead_chars(" .");
            let life = parser.parse(".#.\n..#\n###\n");
            assert_eq!(life.height(), 3);
            assert_eq!(life.width(), 3);
            assert_eq!(
                life.iter_live().collect::<Vec<_>>(),
                [
                    Coords { y: 0, x: 1 },
                    Coords { y: 1, x: 2 },
                    Coords { y: 2, x: 0 },
                    Coords { y: 2, x: 1 },
                    Coords { y: 2, x: 2 }
                ]
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
                [
                    Coords { y: 0, x: 1 },
                    Coords { y: 1, x: 2 },
                    Coords { y: 2, x: 0 },
                    Coords { y: 2, x: 1 },
                    Coords { y: 2, x: 2 }
                ]
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
                [
                    Coords { y: 1, x: 2 },
                    Coords { y: 2, x: 3 },
                    Coords { y: 3, x: 1 },
                    Coords { y: 3, x: 2 },
                    Coords { y: 3, x: 3 }
                ]
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
                [
                    Coords { y: 1, x: 2 },
                    Coords { y: 2, x: 3 },
                    Coords { y: 3, x: 1 },
                    Coords { y: 3, x: 2 },
                    Coords { y: 3, x: 3 }
                ]
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
                [
                    Coords { y: 1, x: 2 },
                    Coords { y: 2, x: 3 },
                    Coords { y: 3, x: 1 },
                    Coords { y: 3, x: 2 },
                    Coords { y: 3, x: 3 }
                ]
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
                [
                    Coords { y: 0, x: 1 },
                    Coords { y: 1, x: 3 },
                    Coords { y: 2, x: 0 },
                    Coords { y: 2, x: 1 },
                    Coords { y: 2, x: 4 }
                ],
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
                [
                    Coords { y: 0, x: 1 },
                    Coords { y: 1, x: 3 },
                    Coords { y: 2, x: 0 },
                    Coords { y: 2, x: 1 },
                    Coords { y: 2, x: 4 },
                    Coords { y: 2, x: 5 },
                    Coords { y: 2, x: 6 }
                ],
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
    }

    #[test]
    fn test_zero_size() {
        let life = Pattern::new(0, 0);
        assert_eq!(life.get((0, 0)), None);
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

    mod edges {
        use super::*;

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

    mod bounds {
        use super::*;

        #[test]
        fn iter_empty() {
            let bounds = Bounds::new(0, 0);
            let mut iter = bounds.into_iter();
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn iter3x2() {
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

        #[test]
        fn union_overlapping() {
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
        fn union_contained() {
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
        fn union_adjacent() {
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
        fn union_non_overlapping() {
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
        fn union_empty_and_nonempty() {
            let b1 = Bounds::new_with_upper_left(2, 4, Coords { y: 5, x: 1 });
            let b2 = Bounds::empty();
            let b3 = b1 | b2;
            assert!(!b3.is_empty());
            assert_eq!(b3, b1);
        }

        #[test]
        fn union_empty_and_empty() {
            let b1 = Bounds::empty();
            let b2 = Bounds::empty();
            let b3 = b1 | b2;
            assert!(b3.is_empty());
            assert_eq!(b3, Bounds::empty());
        }

        #[test]
        fn intersection_overlapping() {
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
        fn intersection_contained() {
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
        fn intersection_adjacent() {
            // .........
            // .###OOOO.
            // .###OOOO.
            // .........
            let b1 = Bounds::new_with_upper_left(2, 3, Coords { y: 1, x: 1 });
            let b2 = Bounds::new_with_upper_left(2, 4, Coords { y: 1, x: 4 });
            let b3 = b1 & b2;
            assert!(b3.is_empty());
            assert_eq!(b3, Bounds::empty());
        }

        #[test]
        fn intersection_non_overlapping() {
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
            assert_eq!(b3, Bounds::empty());
        }

        #[test]
        fn intersection_empty_and_nonempty() {
            let b1 = Bounds::new_with_upper_left(2, 4, Coords { y: 5, x: 1 });
            let b2 = Bounds::empty();
            let b3 = b1 & b2;
            assert!(b3.is_empty());
            assert_eq!(b3, Bounds::empty());
        }

        #[test]
        fn intersection_empty_and_empty() {
            let b1 = Bounds::empty();
            let b2 = Bounds::empty();
            let b3 = b1 & b2;
            assert!(b3.is_empty());
            assert_eq!(b3, Bounds::empty());
        }
    }
}
