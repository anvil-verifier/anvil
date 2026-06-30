#![allow(unused_imports)]
// Verification entry point for the Anvil framework.
//
// Import only the framework modules (no controllers)

use verifiable_controllers::{
    crds,
    external_shim_layer,
    kubernetes_api_objects,
    kubernetes_cluster,
    reconciler,
    shim_layer,
    state_machine,
    temporal_logic,
    tla_demo,
    unit_tests,
    vstd_ext,
};

fn main() {}
