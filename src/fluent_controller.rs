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

use builtin::*;
use builtin_macros::*;

use crate::external_api::exec::*;
use crate::fluent_controller::{
    fluentbit::{
        exec::reconciler::FluentBitReconciler,
        trusted::exec_types::{FluentBit, FluentBitReconcileState},
    },
    fluentbit_config::{
        exec::reconciler::FluentBitConfigReconciler,
        trusted::exec_types::{FluentBitConfig, FluentBitConfigReconcileState},
    },
};
use deps_hack::anyhow::Result;
use deps_hack::futures;
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
        println!("{}", serde_yaml::to_string(&deps_hack::FluentBit::crd())?);
        println!("{}", serde_yaml::to_string(&deps_hack::FluentBitConfig::crd())?);
    } else if cmd == String::from("run") {
        println!("running fluent-controller");
        let fluentbit_controller_fut = run_controller::<deps_hack::FluentBit, FluentBitReconciler>(false);
        let fluentbit_config_controller_fut = run_controller::<deps_hack::FluentBitConfig, FluentBitConfigReconciler>(false);
        futures::try_join!(fluentbit_controller_fut, fluentbit_config_controller_fut)?;
        println!("controller terminated");
    } else if cmd == String::from("crash") {
        println!("running fluent-controller in crash-testing mode");
        let fluentbit_controller_fut = run_controller::<deps_hack::FluentBit, FluentBitReconciler>(true);
        let fluentbit_config_controller_fut = run_controller::<deps_hack::FluentBitConfig, FluentBitConfigReconciler>(true);
        futures::try_join!(fluentbit_controller_fut, fluentbit_config_controller_fut)?;
        println!("controller terminated");
    } else {
        println!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
}
