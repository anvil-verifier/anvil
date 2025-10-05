#![allow(unused_imports)]

use controllers::crds::*;
// use crate::external_shim_layer::VoidExternalShimLayer;
// use crate::vstatefulset_controller::exec::reconciler::VStatefulSetReconciler;
use anyhow::Result;
use kube::CustomResourceExt;
use serde_yaml;
use tokio;
use tracing::{error, info};
use tracing_subscriber;
use verifiable_controllers::shim_layer::controller_runtime::run_controller;
use std::env;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();

    if cmd == String::from("export") {
        println!("{}", serde_yaml::to_string(&VStatefulSet::crd())?);
    // } else if cmd == String::from("run") {
    //     info!("running vstatefulset-controller");
    //     run_controller::<VStatefulSet, VStatefulSetReconciler, VoidExternalShimLayer>(
    //         false,
    //     )
    //     .await?;
    // } else if cmd == String::from("crash") {
    //     info!("running vstatefulset-controller in crash-testing mode");
    //     run_controller::<VStatefulSet, VStatefulSetReconciler, VoidExternalShimLayer>(
    //         true,
    //     )
    //     .await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
