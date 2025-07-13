#![allow(unused_imports)]

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
#[path = "controllers/vdeployment_controller/mod.rs"]
pub mod vdeployment_controller;
pub mod vstd_ext;
#[path = "controllers/vreplicaset_controller/pub_mod.rs"]
pub mod vreplicaset_controller;

// use crate::external_shim_layer::VoidExternalShimLayer;
// use crate::vdeployment_controller::exec::reconciler::VDeploymentReconciler;
use deps_hack::anyhow::Result;
use deps_hack::kube::CustomResourceExt;
use deps_hack::serde_yaml;
use deps_hack::tokio;
use deps_hack::tracing::{error, info};
use deps_hack::tracing_subscriber;
use shim_layer::controller_runtime::run_controller;
use std::env;
use crate::external_shim_layer::VoidExternalShimLayer;
use crate::vdeployment_controller::exec::reconciler::VDeploymentReconciler;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();

    if cmd == String::from("export") {
        println!("{}", serde_yaml::to_string(&deps_hack::VDeployment::crd())?);
    } else if cmd == String::from("run") {
        info!("running vdeployment-controller");
        run_controller::<deps_hack::VDeployment, VDeploymentReconciler, VoidExternalShimLayer>(
            false,
        )
        .await?;
    } else if cmd == String::from("crash") {
        info!("running vdeployment-controller in crash-testing mode");
        run_controller::<deps_hack::VDeployment, VDeploymentReconciler, VoidExternalShimLayer>(
            true,
        )
        .await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
