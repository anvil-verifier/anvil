// pub mod conformance_tests;
// pub mod executable_model;
#[path = "external_shim_layer/mod.rs"]
pub mod external_shim_layer;
pub mod kubernetes_api_objects;
#[path = "kubernetes_cluster/mod.rs"]
pub mod kubernetes_cluster;
#[path = "reconciler/mod.rs"]
pub mod reconciler;
#[path = "shim_layer/mod.rs"]
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;
pub mod unit_tests;
pub mod vstd_ext;

mod tla_demo;

use vstd::prelude::*;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("ShimLayerError: {0}")]
    ShimLayerError(String),
    #[error("ReconcileCoreError")]
    ReconcileCoreError,
}
