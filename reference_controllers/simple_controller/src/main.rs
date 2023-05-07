// Nightly clippy (0.1.64) considers Drop a side effect, see https://github.com/rust-lang/rust-clippy/issues/9608
#![allow(clippy::unnecessary_lazy_evaluations)]

use anyhow::Result;
use futures::StreamExt;
use k8s_openapi::api::core::v1::ConfigMap;
use kube::{
    api::{Api, ListParams, ObjectMeta, PostParams, Resource},
    runtime::controller::{Action, Controller},
    Client, CustomResource,
};
use kube_client;
use kube_core;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use thiserror::Error;
use tokio::time::Duration;
use tracing::*;

#[derive(Debug, Error)]
enum Error {
    #[error("Failed to get CR: {0}")]
    CRGetFailed(#[source] kube::Error),
    #[error("Failed to create ConfigMap: {0}")]
    ConfigMapCreationFailed(#[source] kube::Error),
    #[error("MissingObjectKey: {0}")]
    MissingObjectKey(&'static str),
}

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "SimpleCR")]
#[kube(shortname = "cr", namespaced)]
struct SimpleCRSpec {}

/// Controller triggers this whenever our main object or our children changed
async fn reconcile(cr: Arc<SimpleCR>, ctx: Arc<Data>) -> Result<Action, Error> {
    let client = &ctx.client;

    let cr_name = cr
        .metadata
        .name
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.name"))?;
    let cr_ns = cr
        .metadata
        .namespace
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.namespace"))?;
    let oref = cr.controller_owner_ref(&()).unwrap();

    let cr_api = Api::<SimpleCR>::namespaced(client.clone(), &cr_ns);
    let cm_api = Api::<ConfigMap>::namespaced(client.clone(), &cr_ns);

    cr_api.get(&cr_name).await.map_err(Error::CRGetFailed)?;

    let cm = ConfigMap {
        metadata: ObjectMeta {
            name: Some(cr_name.clone() + "-cm"),
            owner_references: Some(vec![oref]),
            ..ObjectMeta::default()
        },
        data: None,
        ..Default::default()
    };
    let pp = PostParams::default();
    match cm_api.create(&pp, &cm).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ConfigMapCreationFailed(e)),
        },
        _ => {}
    }

    Ok(Action::requeue(Duration::from_secs(300)))
}

/// The controller triggers this on reconcile errors
fn error_policy(_object: Arc<SimpleCR>, _error: &Error, _ctx: Arc<Data>) -> Action {
    Action::requeue(Duration::from_secs(1))
}

// Data we want access to in error/reconcile calls
struct Data {
    client: Client,
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let client = Client::try_default().await?;

    let crs = Api::<SimpleCR>::all(client.clone());

    info!("starting simple-controller");

    Controller::new(crs, ListParams::default())
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { client }))
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => warn!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller terminated");
    Ok(())
}
