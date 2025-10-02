#![allow(unused_imports)]

#[path = "vreplicaset_controller/mod.rs"]
pub mod vreplicaset_controller;

#[path = "vdeployment_controller/mod.rs"]
pub mod vdeployment_controller;

pub mod crds;

use crds::*;
// use crate::external_shim_layer::VoidExternalShimLayer;
// use crate::vdeployment_controller::exec::reconciler::VDeploymentReconciler;
use anyhow::Result;
use kube::CustomResourceExt;
use serde_yaml;
use tokio;
use tracing::{error, info};
use tracing_subscriber;
use verifiable_controllers::shim_layer::controller_runtime::run_controller;
use std::env;
use verifiable_controllers::external_shim_layer::VoidExternalShimLayer;
use vdeployment_controller::exec::reconciler::VDeploymentReconciler;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();

    if cmd == String::from("export") {
        println!("{}", serde_yaml::to_string(&VDeployment::crd())?);
    } else if cmd == String::from("run") {
        info!("running vdeployment-controller");
        run_controller::<VDeployment, VDeploymentReconciler, VoidExternalShimLayer>(
            false,
        )
        .await?;
    } else if cmd == String::from("crash") {
        info!("running vdeployment-controller in crash-testing mode");
        run_controller::<VDeployment, VDeploymentReconciler, VoidExternalShimLayer>(
            true,
        )
        .await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
