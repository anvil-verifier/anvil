// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]

pub mod external_api;
pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
#[path = "controller_examples/rabbitmq_controller/mod.rs"]
pub mod rabbitmq_controller;
pub mod reconciler;
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;
pub mod vstd_ext;

use crate::rabbitmq_controller::exec::reconciler::RabbitmqReconciler;
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
        println!(
            "{}",
            serde_yaml::to_string(&deps_hack::RabbitmqCluster::crd())?
        );
    } else if cmd == String::from("run") {
        info!("running rabbitmq-controller");
        run_controller::<deps_hack::RabbitmqCluster, RabbitmqReconciler>(false).await?;
    } else if cmd == String::from("crash") {
        info!("running rabbitmq-controller in crash-testing mode");
        run_controller::<deps_hack::RabbitmqCluster, RabbitmqReconciler>(true).await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
