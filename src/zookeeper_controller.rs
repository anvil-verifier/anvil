// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]

pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod pervasive_ext;
pub mod reconciler;
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;
#[path = "controller_examples/zookeeper_controller/mod.rs"]
pub mod zookeeper_controller;

use builtin::*;
use builtin_macros::*;

use crate::reconciler::exec::external::*;
use crate::zookeeper_controller::exec::reconciler::{ZookeeperReconcileState, ZookeeperReconciler};
use crate::zookeeper_controller::exec::zookeepercluster::ZookeeperCluster;
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
        println!("{}", serde_yaml::to_string(&deps_hack::ZookeeperCluster::crd())?);
    } else if cmd == String::from("run") {
        println!("running zookeeper-controller");
        run_controller::<deps_hack::ZookeeperCluster, ZookeeperCluster, ZookeeperReconciler, ZookeeperReconcileState,
        EmptyMsg, EmptyMsg, EmptyLib>().await?;
        println!("controller terminated");
    } else {
        println!("wrong command; please use \"export\" or \"run\"");
    }
    Ok(())
}
}
