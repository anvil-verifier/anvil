// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]

#[path = "controller_examples/fluent_controller/mod.rs"]
pub mod fluent_controller;
pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod pervasive_ext;
pub mod reconciler;
pub mod external_api;
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;

use builtin::*;
use builtin_macros::*;

use crate::fluent_controller::exec::fluentbit::FluentBit;
use crate::fluent_controller::exec::reconciler::{FluentBitReconcileState, FluentBitReconciler};
use crate::reconciler::exec::external::*;
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
        println!("{}", serde_yaml::to_string(&deps_hack::FluentBit::crd())?);
    } else if cmd == String::from("run") {
        println!("running fluent-controller");
        run_controller::<deps_hack::FluentBit, FluentBit, FluentBitReconciler, FluentBitReconcileState, EmptyMsg, EmptyMsg, EmptyLib>().await?;
        println!("controller terminated");
    } else {
        println!("wrong command; please use \"export\" or \"run\"");
    }
    Ok(())
}
}
