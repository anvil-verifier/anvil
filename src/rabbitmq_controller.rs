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

use builtin::*;
use builtin_macros::*;

use crate::external_api::exec::*;
use crate::rabbitmq_controller::exec::reconciler::RabbitmqReconciler;
use crate::rabbitmq_controller::trusted::exec_types::{RabbitmqCluster, RabbitmqReconcileState};
use deps_hack::anyhow::Result;
use deps_hack::kube::CustomResourceExt;
use deps_hack::serde_yaml;
use deps_hack::tokio;
use shim_layer::controller_runtime::run_controller;
use std::env;

verus! {

#[verifier(external)]
#[tokio::main]
async fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();

    if cmd == String::from("export") {
        println!("exporting custom resource definition");
        println!("{}", serde_yaml::to_string(&deps_hack::RabbitmqCluster::crd())?);
    } else if cmd == String::from("run") {
        println!("running rabbitmq-controller");
        run_controller::<deps_hack::RabbitmqCluster, RabbitmqReconciler>(false).await?;
        println!("controller terminated");
    } else if cmd == String::from("crash") {
        println!("running rabbitmq-controller in crash-testing mode");
        run_controller::<deps_hack::RabbitmqCluster, RabbitmqReconciler>(true).await?;
        println!("controller terminated");
    } else {
        println!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
}
