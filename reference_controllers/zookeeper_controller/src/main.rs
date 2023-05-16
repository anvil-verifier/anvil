// Nightly clippy (0.1.64) considers Drop a side effect, see https://github.com/rust-lang/rust-clippy/issues/9608
#![allow(clippy::unnecessary_lazy_evaluations)]

pub mod resources;
pub mod zookeepercluster_types;

use anyhow::Result;
use futures::StreamExt;
use k8s_openapi::api::apps::v1 as appsv1;
use k8s_openapi::api::core::v1 as corev1;
use kube::{
    api::{Api, ListParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_client;
use kube_core;
use std::{env, sync::Arc};
use thiserror::Error;
use tokio::time::Duration;
use tracing::*;

use crate::resources::*;
use crate::zookeepercluster_types::*;

#[derive(Debug, Error)]
enum Error {
    #[error("Failed to get CR: {0}")]
    CRGetFailed(#[source] kube::Error),
    #[error("Failed to create ConfigMap: {0}")]
    ConfigMapCreationFailed(#[source] kube::Error),
    #[error("Failed to create Service: {0}")]
    ServiceCreationFailed(#[source] kube::Error),
    #[error("Failed to create StatefulSet: {0}")]
    StatefulSetCreationFailed(#[source] kube::Error),
    #[error("MissingObjectKey: {0}")]
    MissingObjectKey(&'static str),
}

/// Controller triggers this whenever our main object or our children changed
async fn reconcile(zk: Arc<ZookeeperCluster>, ctx: Arc<Data>) -> Result<Action, Error> {
    let client = &ctx.client;

    let zk_name = zk
        .metadata
        .name
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.name"))?;
    let zk_ns = zk
        .metadata
        .namespace
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.namespace"))?;

    let zk_api = Api::<ZookeeperCluster>::namespaced(client.clone(), &zk_ns);
    let svc_api = Api::<corev1::Service>::namespaced(client.clone(), &zk_ns);
    let cm_api = Api::<corev1::ConfigMap>::namespaced(client.clone(), &zk_ns);
    let sts_api = Api::<appsv1::StatefulSet>::namespaced(client.clone(), &zk_ns);

    // Get the ZookeeperCluster custom resource
    zk_api.get(&zk_name).await.map_err(Error::CRGetFailed)?;

    // Create the ZookeeperCluster headless service
    let headless_service = make_headless_service(&zk);
    info!(
        "Create headless service: {}",
        headless_service.metadata.name.as_ref().unwrap()
    );
    match svc_api
        .create(&PostParams::default(), &headless_service)
        .await
    {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ServiceCreationFailed(e)),
        },
        _ => {}
    }

    let client_service = make_client_service(&zk);
    info!(
        "Create client service: {}",
        client_service.metadata.name.as_ref().unwrap()
    );
    match svc_api
        .create(&PostParams::default(), &client_service)
        .await
    {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ServiceCreationFailed(e)),
        },
        _ => {}
    }

    let admin_server_service = make_admin_server_service(&zk);
    info!(
        "Create admin server service: {}",
        admin_server_service.metadata.name.as_ref().unwrap()
    );
    match svc_api
        .create(&PostParams::default(), &admin_server_service)
        .await
    {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ServiceCreationFailed(e)),
        },
        _ => {}
    }

    // Create the ZookeeperCluster configmap
    let cm = make_configmap(&zk);
    match cm_api.create(&PostParams::default(), &cm).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ConfigMapCreationFailed(e)),
        },
        _ => {}
    }

    // Create the ZookeeperCluster statefulset
    let sts = make_statefulset(&zk);
    match sts_api.create(&PostParams::default(), &sts).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::StatefulSetCreationFailed(e)),
        },
        _ => {}
    }

    Ok(Action::requeue(Duration::from_secs(60)))
}

/// The controller triggers this on reconcile errors
fn error_policy(_object: Arc<ZookeeperCluster>, _error: &Error, _ctx: Arc<Data>) -> Action {
    Action::requeue(Duration::from_secs(1))
}

// Data we want access to in error/reconcile calls
struct Data {
    client: Client,
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();
    if cmd == String::from("export") {
        info!("exporting custom resource definition");
        println!("{}", serde_yaml::to_string(&ZookeeperCluster::crd())?);
        Ok(())
    } else if cmd == String::from("run") {
        info!("running zookeeper-controller");
        let client = Client::try_default().await?;
        let zks = Api::<ZookeeperCluster>::all(client.clone());

        Controller::new(zks, ListParams::default())
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
    } else {
        warn!("wrong command; please use \"export\" or \"run\"");
        Ok(())
    }
}
