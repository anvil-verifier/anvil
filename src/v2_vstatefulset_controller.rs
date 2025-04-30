#[path = "v2/external_shim_layer/mod.rs"]
pub mod external_shim_layer;
pub mod kubernetes_api_objects;
#[path = "v2/kubernetes_cluster/mod.rs"]
pub mod kubernetes_cluster;
#[path = "v2/reconciler/mod.rs"]
pub mod reconciler;
#[path = "v2/shim_layer/mod.rs"]
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;
#[path = "v2/controllers/vstatefulset_controller/mod.rs"]
pub mod vstatefulset_controller;
pub mod vstd_ext;

// use crate::external_shim_layer::VoidExternalShimLayer;
// use crate::vstatefulset_controller::exec::reconciler::VStatefulSetReconciler;
use deps_hack::anyhow::Result;
use deps_hack::kube::CustomResourceExt;
use deps_hack::serde_yaml;
use deps_hack::tokio;
use deps_hack::tracing::{error, info};
use deps_hack::tracing_subscriber;
use shim_layer::controller_runtime::run_controller;
use std::env;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();

    if cmd == String::from("export") {
        println!("{}", serde_yaml::to_string(&deps_hack::VStatefulSet::crd())?);
    // } else if cmd == String::from("run") {
    //     info!("running vstatefulset-controller");
    //     run_controller::<deps_hack::VStatefulSet, VStatefulSetReconciler, VoidExternalShimLayer>(
    //         false,
    //     )
    //     .await?;
    // } else if cmd == String::from("crash") {
    //     info!("running vstatefulset-controller in crash-testing mode");
    //     run_controller::<deps_hack::VStatefulSet, VStatefulSetReconciler, VoidExternalShimLayer>(
    //         true,
    //     )
    //     .await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
