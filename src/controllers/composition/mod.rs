pub mod vdeployment_reconciler;
pub mod vreplicaset_reconciler;
pub mod rabbitmq_controller;

// Turn composition into a Verus module
use vstd::prelude::*;


verus! { #[verifier(external_body)] proof fn trivial() {} }