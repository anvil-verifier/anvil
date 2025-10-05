use controllers::crds::*;
use verifiable_controllers::external_shim_layer::VoidExternalShimLayer;
use controllers::vreplicaset_controller::exec::reconciler::VReplicaSetReconciler;
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
        println!("{}", serde_yaml::to_string(&VReplicaSet::crd())?);
    } else if cmd == String::from("run") {
        info!("running vreplicaset-controller");
        run_controller::<VReplicaSet, VReplicaSetReconciler, VoidExternalShimLayer>(
            false,
        )
        .await?;
    } else if cmd == String::from("crash") {
        info!("running vreplicaset-controller in crash-testing mode");
        run_controller::<VReplicaSet, VReplicaSetReconciler, VoidExternalShimLayer>(
            true,
        )
        .await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
