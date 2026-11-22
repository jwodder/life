//! Utility types (mostly iterators)
use crate::errors::{LineFromStringError, ParseLineError};
use crate::{Bounds, Coords, Pattern, State};
use bit_vec::BitVec;
use std::fmt::{self, Write};
use std::iter::FusedIterator;
use std::num::NonZeroUsize;

#[derive(Clone, Debug)]
pub struct RunLengths<'a>(InnerRunLengths<'a>);

#[derive(Clone, Debug)]
enum InnerRunLengths<'a> {
    Runner(Runner<'a>),
    Empty,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Runner<'a> {
    chunks: RowIter<'a>,
    row: Option<Vec<State>>,
}

impl<'a> RunLengths<'a> {
    pub(crate) fn new(life: &'a Pattern) -> RunLengths<'a> {
        if life.width() == 0 {
            // Chunk size must be nonzero
            RunLengths(InnerRunLengths::Empty)
        } else {
            let mut chunks = RowIter::new(&life.cells, life.width());
            let row = chunks.next();
            RunLengths(InnerRunLengths::Runner(Runner { chunks, row }))
        }
    }

    fn runner(&mut self) -> Option<&mut Runner<'a>> {
        match &mut self.0 {
            InnerRunLengths::Runner(runner) => Some(runner),
            InnerRunLengths::Empty => None,
        }
    }
}

impl Runner<'_> {
    fn next_row(&mut self) -> Option<&[State]> {
        self.row = self.chunks.next();
        self.row.as_deref()
    }

    fn next_run_in_row(&mut self) -> Option<Run> {
        if let Some(ref mut row) = self.row {
            let (&current, rest) = row.split_first()?;
            let spanlen = rest.iter().take_while(|&&b| b == current).count();
            row.drain(0..=spanlen);
            let Some(length) = NonZeroUsize::new(spanlen + 1) else {
                unreachable!("1 plus value less than isize::MAX should be nonzero");
            };
            Some(Run {
                length,
                kind: current.into(),
            })
        } else {
            None
        }
    }

    fn at_eol(&self) -> bool {
        self.row.as_ref().is_none_or(Vec::is_empty)
    }

    fn eol_run(&mut self) -> Option<Run> {
        let mut length = 1;
        while self.next_row()?.iter().all(|&st| !st.is_live()) {
            length += 1;
        }
        let Some(length) = NonZeroUsize::new(length) else {
            unreachable!("1 incremented fewer than isize::MAX times should be nonzero");
        };
        Some(Run {
            length,
            kind: RunKind::Eol,
        })
    }
}

impl Iterator for RunLengths<'_> {
    type Item = Run;

    fn next(&mut self) -> Option<Run> {
        let runner = self.runner()?;
        if let Some(item) = runner.next_run_in_row() {
            if runner.at_eol() && item.kind == RunKind::Dead {
                runner.eol_run()
            } else {
                Some(item)
            }
        } else if runner.row.is_none() {
            None
        } else {
            // At EOL
            runner.eol_run()
        }
    }
}

impl FusedIterator for RunLengths<'_> {}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Run {
    pub length: NonZeroUsize,
    pub kind: RunKind,
}

impl Run {
    pub fn display_len(&self) -> usize {
        let digits = if self.length.get() == 1 {
            0
        } else {
            let Ok(x) = usize::try_from(self.length.ilog10()) else {
                unreachable!("The number of digits in a usize should fit in a usize");
            };
            x + 1
        };
        digits + 1
    }
}

impl fmt::Display for Run {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.length.get() != 1 {
            write!(f, "{}", self.length)?;
        }
        write!(f, "{}", self.kind.rle_symbol())?;
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RunKind {
    Dead,
    Live,
    Eol,
}

impl RunKind {
    pub fn rle_symbol(&self) -> char {
        match self {
            RunKind::Dead => 'b',
            RunKind::Live => 'o',
            RunKind::Eol => '$',
        }
    }

    pub fn as_state(&self) -> Option<State> {
        match self {
            RunKind::Dead => Some(State::Dead),
            RunKind::Live => Some(State::Live),
            RunKind::Eol => None,
        }
    }
}

impl From<State> for RunKind {
    fn from(st: State) -> RunKind {
        match st {
            State::Dead => RunKind::Dead,
            State::Live => RunKind::Live,
        }
    }
}

#[expect(missing_debug_implementations)]
#[derive(Clone)]
pub struct Enumerate<'a> {
    coords: BoundsIntoIter,
    inner: bit_vec::Iter<'a, u32>,
}

impl<'a> Enumerate<'a> {
    pub(crate) fn new(life: &'a Pattern) -> Enumerate<'a> {
        Enumerate {
            coords: life.bounds.into_iter(),
            inner: life.cells.iter(),
        }
    }
}

impl Iterator for Enumerate<'_> {
    type Item = (Coords, State);

    fn next(&mut self) -> Option<(Coords, State)> {
        let c = self.coords.next()?;
        let b = self.inner.next()?;
        Some((c, State::living(b)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl ExactSizeIterator for Enumerate<'_> {}

impl FusedIterator for Enumerate<'_> {}

#[expect(missing_debug_implementations)]
#[derive(Clone)]
pub struct IterLive<'a> {
    inner: Enumerate<'a>,
}

impl<'a> IterLive<'a> {
    pub(crate) fn new(life: &'a Pattern) -> IterLive<'a> {
        IterLive {
            inner: Enumerate::new(life),
        }
    }
}

impl Iterator for IterLive<'_> {
    type Item = Coords;

    fn next(&mut self) -> Option<Coords> {
        for (yx, b) in self.inner.by_ref() {
            if b.is_live() {
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

impl FusedIterator for IterLive<'_> {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Generations(pub(crate) Pattern);

impl Iterator for Generations {
    type Item = Pattern;

    fn next(&mut self) -> Option<Pattern> {
        let mut life = self.0.step();
        std::mem::swap(&mut self.0, &mut life);
        Some(life)
    }
}

impl FusedIterator for Generations {}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Draw<'a> {
    life: &'a Pattern,
    dead: char,
    live: char,
}

impl<'a> Draw<'a> {
    pub(crate) fn new(life: &'a Pattern, dead: char, live: char) -> Draw<'a> {
        Draw { life, dead, live }
    }
}

impl fmt::Display for Draw<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ul = self.life.upper_left();
        for (c, b) in self.life.enumerate() {
            if c.x == ul.x && c.y > ul.y {
                f.write_char('\n')?;
            }
            f.write_char(if b.is_live() { self.live } else { self.dead })?;
        }
        Ok(())
    }
}

#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Line(String);

impl Line {
    pub fn push_line(&mut self, line: &Line) {
        self.0.push_str(&line.0);
    }
}

impl From<Line> for String {
    fn from(value: Line) -> String {
        value.0
    }
}

impl From<&Line> for String {
    fn from(value: &Line) -> String {
        value.0.clone()
    }
}

impl fmt::Debug for Line {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl fmt::Display for Line {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl PartialEq<str> for Line {
    fn eq(&self, other: &str) -> bool {
        self.0 == other
    }
}

impl<'a> PartialEq<&'a str> for Line {
    fn eq(&self, other: &&'a str) -> bool {
        &self.0 == other
    }
}

impl AsRef<str> for Line {
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}

impl std::ops::Deref for Line {
    type Target = str;

    fn deref(&self) -> &str {
        &self.0
    }
}

impl std::str::FromStr for Line {
    type Err = ParseLineError;

    fn from_str(s: &str) -> Result<Line, ParseLineError> {
        check_for_newlines(s).map(|()| Line(s.to_owned()))
    }
}

impl TryFrom<String> for Line {
    type Error = LineFromStringError;

    fn try_from(string: String) -> Result<Line, LineFromStringError> {
        match check_for_newlines(&string) {
            Ok(()) => Ok(Line(string)),
            Err(source) => Err(LineFromStringError { source, string }),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoundsIntoIter {
    bounds: Bounds,
    y: isize,
    x: isize,
}

impl BoundsIntoIter {
    pub(crate) fn new(bounds: Bounds) -> BoundsIntoIter {
        BoundsIntoIter {
            bounds,
            y: bounds.upper_left.y,
            x: bounds.upper_left.x,
        }
    }
}

impl Iterator for BoundsIntoIter {
    type Item = Coords;

    fn next(&mut self) -> Option<Coords> {
        let lr = self.bounds.lower_right();
        if self.y >= lr.y {
            return None;
        }
        let c = Coords {
            y: self.y,
            x: self.x,
        };
        self.x += 1;
        if self.x >= lr.x {
            self.x = self.bounds.upper_left.x;
            self.y += 1;
        }
        Some(c)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let lr = self.bounds.lower_right();
        let sz = if self.y >= lr.y {
            0
        } else {
            lr.x.abs_diff(self.x).saturating_add(
                self.bounds
                    .width
                    .saturating_mul(lr.y.abs_diff(self.y.saturating_add(1))),
            )
        };
        (sz, Some(sz))
    }
}

impl ExactSizeIterator for BoundsIntoIter {}

impl FusedIterator for BoundsIntoIter {}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RowIter<'a> {
    cells: &'a BitVec,
    width: usize,
    i: usize,
}

impl<'a> RowIter<'a> {
    fn new(cells: &'a BitVec, width: usize) -> Self {
        RowIter { cells, width, i: 0 }
    }
}

impl Iterator for RowIter<'_> {
    type Item = Vec<State>;

    fn next(&mut self) -> Option<Vec<State>> {
        (self.i < self.cells.len()).then(|| {
            let mut row = Vec::with_capacity(self.width);
            for _ in 0..self.width {
                row.push(State::living(self.cells[self.i]));
                self.i += 1;
            }
            row
        })
    }
}

fn check_for_newlines(s: &str) -> Result<(), ParseLineError> {
    match s.chars().find(|&c| {
        matches!(
            c,
            '\n' | '\r' | '\x0B' | '\x0C' | '\u{85}' | '\u{2028}' | '\u{2029}'
        )
    }) {
        Some(c) => Err(ParseLineError(c)),
        None => Ok(()),
    }
}
