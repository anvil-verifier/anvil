// pub mod exec;
// pub mod model;
// pub mod proof;
pub mod trusted;

use vstd::prelude::*;

verus! { proof fn trivial() ensures true {} }
