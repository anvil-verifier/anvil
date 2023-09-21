// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]

pub mod external_api;
pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod pervasive_ext;
pub mod reconciler;
pub mod shim_layer;
#[path = "controller_examples/simple_controller/mod.rs"]
pub mod simple_controller;
pub mod state_machine;
pub mod temporal_logic;

use builtin::*;
use builtin_macros::*;

use crate::external_api::exec::*;
use crate::simple_controller::exec::reconciler::{SimpleReconcileState, SimpleReconciler};
use crate::simple_controller::spec::custom_resource::SimpleCR;
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
        println!("{}", serde_yaml::to_string(&deps_hack::SimpleCR::crd())?);
    } else if cmd == String::from("run") {
        println!("running simple-controller");
        run_controller::<deps_hack::SimpleCR, SimpleCR, SimpleReconciler, SimpleReconcileState, EmptyType, EmptyType, EmptyAPIShimLayer>(false).await?;
        println!("controller terminated");
    } else if cmd == String::from("crash") {
        println!("running simple-controller in crash-testing mode");
        run_controller::<deps_hack::SimpleCR, SimpleCR, SimpleReconciler, SimpleReconcileState, EmptyType, EmptyType, EmptyAPIShimLayer>(true).await?;
        println!("controller terminated");
    } else {
        println!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
}
