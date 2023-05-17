// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]

pub mod controller_examples;
pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod pervasive_ext;
pub mod reconciler;
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;

use builtin::*;
use builtin_macros::*;

use crate::controller_examples::simple_controller::exec::reconciler::{
    SimpleReconcileState, SimpleReconciler,
};
use anyhow::Result;
use deps_hack::SimpleCR;
use kube::CustomResourceExt;
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
        println!("{}", serde_yaml::to_string(&SimpleCR::crd())?);
    } else if cmd == String::from("run") {
        println!("running simple-controller");
        run_controller::<SimpleCR, SimpleReconciler, SimpleReconcileState>().await?;
        println!("controller terminated");
    } else {
        println!("wrong command; please use \"export\" or \"run\"");
    }
    Ok(())
}
}
