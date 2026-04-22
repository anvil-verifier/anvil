pub mod common;
pub mod vreplicaset_reconciler;
pub mod vdeployment_reconciler;
pub mod vstatefulset_reconciler;
pub mod rabbitmq_reconciler;
pub mod compose_all;

// Turn composition into a Verus module
use vstd::prelude::*;


verus! { spec fn trivial() ->bool {true} } // makes verus recognize this as a mod
