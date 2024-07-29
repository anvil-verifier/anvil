// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]

#[path = "controller_examples/composition_example/consumer_controller/mod.rs"]
pub mod consumer_controller;
pub mod external_api;
pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
#[path = "controller_examples/composition_example/producer_controller/mod.rs"]
pub mod producer_controller;
pub mod reconciler;
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;
pub mod vstd_ext;

use crate::consumer_controller::exec::reconciler::ConsumerReconciler;
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
        println!("{}", serde_yaml::to_string(&deps_hack::Consumer::crd())?);
    } else if cmd == String::from("run") {
        info!("running consumer-controller");
        run_controller::<deps_hack::Consumer, ConsumerReconciler>(false).await?;
    } else if cmd == String::from("crash") {
        info!("running consumer-controller in crash-testing mode");
        run_controller::<deps_hack::Consumer, ConsumerReconciler>(true).await?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
