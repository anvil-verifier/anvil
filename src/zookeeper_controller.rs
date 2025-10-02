// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]

pub mod external_api;
pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod reconciler;
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;
pub mod vstd_ext;
#[path = "controller_examples/zookeeper_controller/mod.rs"]
pub mod zookeeper_controller;

use crate::zookeeper_controller::exec::reconciler::ZookeeperReconciler;
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
            serde_yaml::to_string(&deps_hack::ZookeeperCluster::crd())?
        );
    } else if cmd == String::from("run") {
        info!("running zookeeper-controller");
        run_controller::<deps_hack::ZookeeperCluster, ZookeeperReconciler>(false).await?;
    } else if cmd == String::from("crash") {
        info!("running zookeeper-controller in crash-testing mode");
        run_controller::<deps_hack::ZookeeperCluster, ZookeeperReconciler>(true).await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
