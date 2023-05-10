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
use shim_layer::run_controller;

verus! {

#[verifier(external)]
#[tokio::main]
async fn main() -> Result<()> {
    println!("This is main");

    run_controller::<SimpleCR, SimpleReconciler, SimpleReconcileState>().await?;
    Ok(())
}
}
