#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

pub enum ABC {
    A,
    B,
    C,
}

pub struct SimpleState {
    pub x: ABC,
    pub happy: bool,
}

pub struct StatePair {
    pub state_0: SimpleState,
    pub state_1: SimpleState,
}

}
