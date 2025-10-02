// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]

pub mod external_api;
#[path = "controller_examples/fluent_controller/mod.rs"]
pub mod fluent_controller;
pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod reconciler;
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;
pub mod vstd_ext;

use crate::fluent_controller::{
    fluentbit::exec::reconciler::FluentBitReconciler,
    fluentbit_config::exec::reconciler::FluentBitConfigReconciler,
};
use deps_hack::anyhow::Result;
use deps_hack::futures;
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
        println!("{}", serde_yaml::to_string(&deps_hack::FluentBit::crd())?);
        println!(
            "{}",
            serde_yaml::to_string(&deps_hack::FluentBitConfig::crd())?
        );
    } else if cmd == String::from("run") {
        info!("running fluent-controller");
        let fluentbit_controller_fut =
            run_controller::<deps_hack::FluentBit, FluentBitReconciler>(false);
        let fluentbit_config_controller_fut =
            run_controller::<deps_hack::FluentBitConfig, FluentBitConfigReconciler>(false);
        futures::try_join!(fluentbit_controller_fut, fluentbit_config_controller_fut)?;
    } else if cmd == String::from("crash") {
        info!("running fluent-controller in crash-testing mode");
        let fluentbit_controller_fut =
            run_controller::<deps_hack::FluentBit, FluentBitReconciler>(true);
        let fluentbit_config_controller_fut =
            run_controller::<deps_hack::FluentBitConfig, FluentBitConfigReconciler>(true);
        futures::try_join!(fluentbit_controller_fut, fluentbit_config_controller_fut)?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
