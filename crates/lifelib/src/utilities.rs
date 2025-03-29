//! Utility types (mostly iterators)
use crate::errors::{LineFromStringError, ParseLineError};
use crate::{Pattern, State};
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

#[derive(Clone, Debug)]
struct Runner<'a> {
    chunks: std::slice::ChunksExact<'a, State>,
    row: Option<&'a [State]>,
}

impl<'a> RunLengths<'a> {
    pub(crate) fn new(life: &'a Pattern) -> RunLengths<'a> {
        if life.width == 0 {
            // Chunk size must be nonzero
            RunLengths(InnerRunLengths::Empty)
        } else {
            let mut chunks = life.cells.chunks_exact(life.width);
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

impl<'a> Runner<'a> {
    fn next_row(&mut self) -> Option<&'a [State]> {
        self.row = self.chunks.next();
        self.row
    }

    fn next_run_in_row(&mut self) -> Option<Run> {
        let (&current, rest) = self.row?.split_first()?;
        let spanlen = rest.iter().take_while(|&&b| b == current).count();
        self.row = Some(&rest[spanlen..]);
        let Some(length) = NonZeroUsize::new(spanlen + 1) else {
            unreachable!("1 plus value less than isize::MAX should be nonzero");
        };
        Some(Run {
            length,
            run_type: current.into(),
        })
    }

    fn at_eol(&self) -> bool {
        self.row.map_or(true, <[State]>::is_empty)
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
            run_type: RunType::Eol,
        })
    }
}

impl Iterator for RunLengths<'_> {
    type Item = Run;

    fn next(&mut self) -> Option<Run> {
        let runner = self.runner()?;
        if let Some(item) = runner.next_run_in_row() {
            if runner.at_eol() && item.run_type == RunType::Dead {
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
    pub run_type: RunType,
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
        write!(f, "{}", self.run_type.rle_symbol())?;
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RunType {
    Dead,
    Live,
    Eol,
}

impl RunType {
    pub fn rle_symbol(&self) -> char {
        match self {
            RunType::Dead => 'b',
            RunType::Live => 'o',
            RunType::Eol => '$',
        }
    }

    pub fn as_state(&self) -> Option<State> {
        match self {
            RunType::Dead => Some(State::Dead),
            RunType::Live => Some(State::Live),
            RunType::Eol => None,
        }
    }
}

impl From<State> for RunType {
    fn from(st: State) -> RunType {
        match st {
            State::Dead => RunType::Dead,
            State::Live => RunType::Live,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Enumerate<'a> {
    y: usize,
    x: usize,
    width: usize,
    inner: std::slice::Iter<'a, State>,
}

impl<'a> Enumerate<'a> {
    pub(crate) fn new(life: &'a Pattern) -> Enumerate<'a> {
        Enumerate {
            y: 0,
            x: 0,
            width: life.width(),
            inner: life.cells.iter(),
        }
    }
}

impl Iterator for Enumerate<'_> {
    type Item = ((usize, usize), State);

    fn next(&mut self) -> Option<((usize, usize), State)> {
        let &b = self.inner.next()?;
        let old_y = self.y;
        let old_x = self.x;
        // These operations won't overflow, as neither of x and y will get past
        // isize::MAX, the maximum capacity of a Vec.
        self.x += 1;
        if self.x >= self.width {
            self.x = 0;
            self.y += 1;
        }
        Some(((old_y, old_x), b))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl ExactSizeIterator for Enumerate<'_> {}

impl FusedIterator for Enumerate<'_> {}

#[derive(Clone, Debug)]
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
    type Item = (usize, usize);

    fn next(&mut self) -> Option<(usize, usize)> {
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
        for ((y, x), b) in self.life.enumerate() {
            if x == 0 && y > 0 {
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
