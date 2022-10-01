// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
use builtin::*;
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

pub struct Action {
    pub state_0: SimpleState,
    pub state_1: SimpleState,
}

pub type Execution = Seq<SimpleState>;

pub type StatePred = Set<SimpleState>;
pub type ActionPred = Set<Action>;
pub type TempPred = Set<Execution>;


}
