// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]

pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod pervasive_ext;
#[path = "controller_examples/rabbitmq_controller/mod.rs"]
pub mod rabbitmq_controller;
pub mod reconciler;
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;

use builtin::*;
use builtin_macros::*;

use crate::rabbitmq_controller::exec::reconciler::{RabbitmqReconcileState, RabbitmqReconciler};
use crate::rabbitmq_controller::spec::rabbitmqcluster::RabbitmqCluster;
use deps_hack::anyhow::Result;
use deps_hack::kube::CustomResourceExt;
use deps_hack::serde_yaml;
use deps_hack::tokio;
use shim_layer::run_controller;
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
<<<<<<< HEAD
        run_controller::<deps_hack::RabbitmqCluster, RabbitmqCluster, RabbitmqReconciler, RabbitmqReconcileState>().await?;
=======
        run_controller::<deps_hack::RabbitmqCluster, RabbitmqReconciler, RabbitmqReconcileState>().await?;
>>>>>>> b8a1e542db70b308f60f81e1fac35e492983f6b6
        println!("controller terminated");
    } else {
        println!("wrong command; please use \"export\" or \"run\"");
    }
    Ok(())
}
}
