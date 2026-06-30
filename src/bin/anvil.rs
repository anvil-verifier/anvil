#![allow(unused_imports)]
// Verification entry point for the Anvil framework.
//
// This binary declares only the framework modules (no controllers), so that
//     cargo verus focus --bin anvil -- --rlimit 50 --time
// verifies the framework on its own instead of re-verifying every controller
// (which each have their own verification job). The TLA demo lives here too and
// can be verified in isolation with `--verify-only-module tla_demo`.

#[path = "../crds.rs"]
pub mod crds;
#[path = "../external_shim_layer/mod.rs"]
pub mod external_shim_layer;
#[path = "../kubernetes_api_objects/mod.rs"]
pub mod kubernetes_api_objects;
#[path = "../kubernetes_cluster/mod.rs"]
pub mod kubernetes_cluster;
#[path = "../reconciler/mod.rs"]
pub mod reconciler;
#[path = "../shim_layer/mod.rs"]
pub mod shim_layer;
#[path = "../state_machine/mod.rs"]
pub mod state_machine;
#[path = "../temporal_logic/mod.rs"]
pub mod temporal_logic;
#[path = "../unit_tests/mod.rs"]
pub mod unit_tests;
#[path = "../vstd_ext/mod.rs"]
pub mod vstd_ext;

#[path = "../tla_demo.rs"]
pub mod tla_demo;

fn main() {}
