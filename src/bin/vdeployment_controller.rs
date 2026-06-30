#![allow(unused_imports)]

use anyhow::Result;
use kube::CustomResourceExt;
use std::env;
use tracing::{error, info};
use verifiable_controllers::crds::{VDeployment, VReplicaSet};
use verifiable_controllers::external_shim_layer::VoidExternalShimLayer;
use verifiable_controllers::shim_layer::controller_runtime::run_controller_watching_owned;
use verifiable_controllers::vdeployment_controller::exec::reconciler::VDeploymentReconciler;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();

    if cmd == String::from("export") {
        println!("{}", serde_yaml::to_string(&VDeployment::crd())?);
    } else if cmd == String::from("run") {
        info!("running vdeployment-controller");
        run_controller_watching_owned::<VDeployment, VDeploymentReconciler, VoidExternalShimLayer, VReplicaSet>(
            false,
        )
        .await?;
    } else if cmd == String::from("crash") {
        info!("running vdeployment-controller in crash-testing mode");
        run_controller_watching_owned::<VDeployment, VDeploymentReconciler, VoidExternalShimLayer, VReplicaSet>(
            true,
        )
        .await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
