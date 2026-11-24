use crate::{BoundsError, Coords, Edges, Pattern, State};

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

    pub fn build(self) -> Result<Pattern, BoundsError> {
        let mut pat = Pattern::try_new(self.height, self.width)?.with_edges(self.edges);
        for c in self.live {
            pat.birth(c);
        }
        Ok(pat)
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
    /// let life = parser.parse(".#?\n..#\n###\n").unwrap();
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
    /// let life = parser.parse(".#?\n..#\n###\n").unwrap();
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
    pub fn parse(&self, s: &str) -> Result<Pattern, BoundsError> {
        let mut builder = PatternBuilder::new()
            .edges(self.edges)
            .min_height(self.min_height)
            .min_width(self.min_width)
            .max_height(self.max_height)
            .max_width(self.max_width);
        // TODO: Document behavior for large input
        for (y, line) in s.lines().enumerate().take(self.max_height) {
            // Ensure that trailing dead rows count towards the height:
            builder = builder.min_height(y + 1);
            for (x, ch) in line.chars().enumerate().take(self.max_width) {
                // Ensure that trailing dead cells count towards the width:
                builder = builder.min_width(x + 1);
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

#[cfg(test)]
mod tests {
    use super::*;

    mod builder {
        use super::*;
        #[test]
        fn test_empty_builder() {
            let builder = PatternBuilder::new();
            let life = builder.build().unwrap();
            assert_eq!(life.height(), 0);
            assert_eq!(life.width(), 0);
            assert_eq!(life.draw('.', '#').to_string(), "");
        }

        #[test]
        fn test_empty_builder_min_height() {
            let builder = PatternBuilder::new().min_height(1);
            let life = builder.build().unwrap();
            // The height is zero because the width was zero, so both dimensions
            // are zeroed.
            assert_eq!(life.height(), 0);
            assert_eq!(life.width(), 0);
            assert_eq!(life.draw('.', '#').to_string(), "");
        }
    }

    mod parser {
        use super::*;

        #[test]
        fn test_parse1() {
            let parser = PatternParser::dead_chars(" .");
            let life = parser.parse(".#.\n..#\n###\n").unwrap();
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
            let life = parser.parse(".#.\n..#\n###\n").unwrap();
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
            let life = parser.parse(".....\n..#..\n...#.\n.###.\n.....").unwrap();
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
            let life = parser.parse("\n..#\n...#\n.###\n").unwrap();
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
            let life = parser.parse("\n..#\n...#\n.###\n").unwrap();
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
            let life = parser.parse(" +\n   +\n++  +++\n").unwrap();
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
            let life = parser.parse(" +\n   +\n++  +++\n+ + + + + + +\n").unwrap();
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
            )).unwrap();
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
}
