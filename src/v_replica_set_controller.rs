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
#[path = "controller_examples/v_replica_set_controller/mod.rs"]
pub mod v_replica_set_controller;
pub mod vstd_ext;

use builtin::*;
use builtin_macros::*;

use crate::external_api::exec::*;
use crate::v_replica_set_controller::exec::reconciler::VReplicaSetReconciler;
use crate::v_replica_set_controller::trusted::exec_types::{
    VReplicaSet, VReplicaSetReconcileState,
};
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
        println!("{}", serde_yaml::to_string(&deps_hack::VReplicaSet::crd())?);
    } else if cmd == String::from("run") {
        println!("running v-replica-set-controller");
        run_controller::<deps_hack::VReplicaSet, VReplicaSetReconciler>(false).await?;
        println!("controller terminated");
    } else if cmd == String::from("crash") {
        println!("running v-replica-set-controller in crash-testing mode");
        run_controller::<deps_hack::VReplicaSet, VReplicaSetReconciler>(true).await?;
        println!("controller terminated");
    } else {
        println!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
}
