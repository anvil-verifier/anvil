pub mod exec;
pub mod model;
// pub mod proof;
pub mod trusted;

#[path = "../crds/mod.rs"]
mod crds;

use vstd::prelude::*;
use crds::*;

verus! { proof fn trivial() ensures true {} }
