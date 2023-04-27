// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#![allow(unused_imports)]

pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod pervasive_ext;
pub mod shim_layer;
pub mod simple_controller;
pub mod state_machine;
pub mod temporal_logic;

use builtin::*;
use builtin_macros::*;

use anyhow::Result;
use deps_hack::{Error, SimpleCR};
use futures::StreamExt;
use kube::{
    api::{Api, ListParams, ObjectMeta, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use shim_layer::reconcile::{reconcile, Data};
use std::sync::Arc;
use std::time::Duration;
use tracing::*;

verus! {

#[verifier(external)]
fn error_policy(_object: Arc<SimpleCR>, _error: &Error, _ctx: Arc<Data>) -> Action {
    Action::requeue(Duration::from_secs(1))
}

#[verifier(external)]
#[tokio::main]
async fn main() -> Result<()> {
    println!("This is main");

    let client = Client::try_default().await?;
    let crs = Api::<SimpleCR>::all(client.clone());
    println!(
        "Simple CRD:\n{}\n",
        serde_yaml::to_string(&SimpleCR::crd())?
    );

    println!("starting simple-controller");
    Controller::new(crs, ListParams::default()) // The controller's reconcile is triggered when a CR is created/updated
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { client })) // The reconcile function is registered
        .for_each(|res| async move {
            match res {
                Ok(o) => println!("reconciled {:?}", o),
                Err(e) => println!("reconcile failed: {}", e),
            }
        })
        .await;
    println!("controller terminated");
    Ok(())
}
}
