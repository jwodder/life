use crate::{
    Bounds, BoundsError, Coords, Edges, State,
    utilities::{Draw, Enumerate, Generations, IterCoords, IterLive, RunLengths, TryGenerations},
};
use bit_vec::BitVec;
use std::ops::Range;
use thiserror::Error;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pattern {
    pub(crate) bounds: Bounds,
    pub(crate) edges: Edges,
    pub(crate) cells: BitVec,
}

impl Pattern {
    /// # Panics
    ///
    /// Panics if either `width` or `height` exceeds [`isize::MAX`] or if
    /// `width * height` exceeds [`usize::MAX`]
    pub fn new(height: usize, width: usize) -> Pattern {
        match Pattern::try_new(height, width) {
            Ok(p) => p,
            Err(e) => panic!("failed to construct Pattern: {e}"),
        }
    }

    pub fn try_new(height: usize, width: usize) -> Result<Pattern, BoundsError> {
        let bounds = Bounds::try_new(height, width)?;
        let cells = BitVec::from_elem(height * width, false);
        Ok(Pattern {
            bounds,
            edges: Edges::default(),
            cells,
        })
    }

    pub fn new_with_bounds(bounds: Bounds) -> Pattern {
        Pattern {
            bounds,
            edges: Edges::default(),
            cells: BitVec::from_elem(bounds.height * bounds.width, false),
        }
    }

    pub fn bounds(&self) -> Bounds {
        self.bounds
    }

    pub fn height(&self) -> usize {
        self.bounds.height()
    }

    pub fn width(&self) -> usize {
        self.bounds.width()
    }

    pub fn upper_left(&self) -> Coords {
        self.bounds.upper_left()
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
        match self.try_step() {
            Ok(p) => p,
            Err(e) => panic!("failed to calculate next step of pattern: {e}"),
        }
    }

    pub fn try_step(&self) -> Result<Pattern, StepError> {
        let mut next_state = self.clone();
        let yrange = grow_range(self.bounds.yrange(), self.edges.grows_y())?;
        let xrange = grow_range(self.bounds.xrange(), self.edges.grows_x())?;
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
                        next_state.ensure_contains(c)?;
                        next_state.birth(c);
                    }
                    4 => (),
                    _ => next_state.kill(c),
                }
            }
        }
        Ok(next_state)
    }

    fn ensure_contains<C: Into<Coords>>(&mut self, c: C) -> Result<(), BoundsError> {
        let new_bounds = self
            .bounds
            .try_union(Bounds::try_new_with_upper_left(1, 1, c.into())?)?;
        if new_bounds != self.bounds {
            *self = self.resize(new_bounds);
        }
        Ok(())
    }

    pub fn into_generations(self) -> Generations {
        Generations(self)
    }

    pub fn into_try_generations(self) -> TryGenerations {
        TryGenerations::new(self)
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

    pub fn moved_to<C: Into<Coords>>(&self, c: C) -> Result<Pattern, BoundsError> {
        let bounds = self.bounds.moved_to(c)?;
        Ok(Pattern {
            bounds,
            edges: self.edges,
            cells: self.cells.clone(),
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, Error, PartialEq)]
pub enum StepError {
    #[error("numeric overflow while growing pattern bounds")]
    Overflow,
    #[error("overflow while growing pattern bounds")]
    Bounds(#[from] BoundsError),
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

fn grow_range(range: Range<isize>, grow: bool) -> Result<Range<isize>, StepError> {
    if grow {
        let start = range.start.checked_sub(1).ok_or(StepError::Overflow)?;
        let end = range.end.checked_add(1).ok_or(StepError::Overflow)?;
        Ok(start..end)
    } else {
        Ok(range)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PatternParser;
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
                ))
                .unwrap();
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
        )).unwrap();
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
}
