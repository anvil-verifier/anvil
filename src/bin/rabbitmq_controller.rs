// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]

use anyhow::Result;
use kube::CustomResourceExt;
use std::env;
use tracing::{error, info};
use verifiable_controllers::crds::RabbitmqCluster;
use verifiable_controllers::external_shim_layer::VoidExternalShimLayer;
use verifiable_controllers::rabbitmq_controller::exec::reconciler::RabbitmqReconciler;
use verifiable_controllers::shim_layer::controller_runtime::run_controller;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();

    if cmd == String::from("export") {
        println!("{}", serde_yaml::to_string(&RabbitmqCluster::crd())?);
    } else if cmd == String::from("run") {
        info!("running rabbitmq-controller");
        run_controller::<RabbitmqCluster, RabbitmqReconciler, VoidExternalShimLayer>(false)
            .await?;
    } else if cmd == String::from("crash") {
        info!("running rabbitmq-controller in crash-testing mode");
        run_controller::<RabbitmqCluster, RabbitmqReconciler, VoidExternalShimLayer>(true)
            .await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
