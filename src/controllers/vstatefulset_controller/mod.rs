pub mod exec;
pub mod model;
pub mod proof;
pub mod trusted;

use vstd::prelude::*;

verus! { spec fn trivial() ->bool {true} } // makes verus recognize this as a mod