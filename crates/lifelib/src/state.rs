use std::ops::{BitAnd, BitOr, BitXor, Not};

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
