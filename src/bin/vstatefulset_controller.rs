#![allow(unused_imports)]

use anyhow::Result;
use k8s_openapi::api::core::v1::PersistentVolumeClaim;
use kube::CustomResourceExt;
use std::env;
use tracing::{error, info};
use verifiable_controllers::crds::VStatefulSet;
use verifiable_controllers::external_shim_layer::VoidExternalShimLayer;
use verifiable_controllers::shim_layer::controller_runtime::run_controller_watching_owned;
use verifiable_controllers::vstatefulset_controller::exec::reconciler::VStatefulSetReconciler;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();

    if cmd == String::from("export") {
        println!("{}", serde_yaml::to_string(&VStatefulSet::crd())?);
    } else if cmd == String::from("run") {
        info!("running vstatefulset-controller");
        run_controller_watching_owned::<
            VStatefulSet,
            VStatefulSetReconciler,
            VoidExternalShimLayer,
            PersistentVolumeClaim,
        >(false)
        .await?;
    } else if cmd == String::from("crash") {
        info!("running vstatefulset-controller in crash-testing mode");
        run_controller_watching_owned::<
            VStatefulSet,
            VStatefulSetReconciler,
            VoidExternalShimLayer,
            PersistentVolumeClaim,
        >(true)
        .await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
