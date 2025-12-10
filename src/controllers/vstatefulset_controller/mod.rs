pub mod exec;
pub mod model;
// pub mod proof;
pub mod trusted;

use vstd::prelude::*;

verus! { #[verifier(external_body)] proof fn trivial() {} } // makes verus recognize this as a mod