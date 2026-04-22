pub mod common;
pub mod vreplicaset_reconciler;
// pub mod vdeployment_reconciler;
// pub mod rabbitmq_controller;
// pub mod vstatefulset_controller;

// Turn composition into a Verus module
use vstd::prelude::*;


verus! { spec fn trivial() ->bool {true} } // makes verus recognize this as a mod
