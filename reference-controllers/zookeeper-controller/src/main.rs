// Nightly clippy (0.1.64) considers Drop a side effect, see https://github.com/rust-lang/rust-clippy/issues/9608
#![allow(clippy::unnecessary_lazy_evaluations)]

pub mod common;
pub mod resources;
pub mod zookeepercluster_types;

use anyhow::Result;
use futures::StreamExt;
use k8s_openapi::api::apps::v1::{self as appsv1, StatefulSet};
use k8s_openapi::api::core::v1::{self as corev1, ConfigMap};
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
use zookeeper::{Acl, CreateMode, WatchedEvent, Watcher, ZkError, ZooKeeper};

use crate::common::{cluster_size_zk_node_path, zk_service_uri};
use crate::resources::*;
use crate::zookeepercluster_types::*;

use zookeeper_client as zk;
use zookeeper_client::EnsembleUpdate;

#[derive(Debug, Error)]
enum Error {
    #[error("Failed to get CR: {0}")]
    CRGetFailed(#[source] kube::Error),
    #[error("Failed to reconcile ConfigMap: {0}")]
    ReconcileConfigMapFailed(#[source] kube::Error),
    #[error("Failed to reconcile Service: {0}")]
    ReconcileServiceFailed(#[source] kube::Error),
    #[error("Failed to reconcile StatefulSet: {0}")]
    ReconcileStatefulSetFailed(#[source] kube::Error),
    #[error("Failed to send commands through zk-client: {0}")]
    ZkClientCommandFailed(#[source] zk::Error),
    #[error("Failed to connect ZK cluster: {0}")]
    ZkClusterConnectFailed(#[source] zk::ConnectError),
    #[error("Failed to get StatefulSet: {0}")]
    GetStatefulSetFailed(#[source] kube::Error),
    #[error("Failed to reconcile the zk node to store cluster size: {0}")]
    ClusterSizeZKNodeCreationFailed(#[source] ZkError),
    #[error("MissingObjectKey: {0}")]
    MissingObjectKey(&'static str),
}

struct LoggingWatcher;
impl Watcher for LoggingWatcher {
    fn handle(&self, e: WatchedEvent) {
        info!("{:?}", e)
    }
}

async fn reconcile_headless_service(zk: &ZookeeperCluster, client: Client) -> Result<(), Error> {
    // Create the ZookeeperCluster headless service.
    // The headless service is used to assign a domain name for each zookeeper replica.
    let svc_api =
        Api::<corev1::Service>::namespaced(client.clone(), zk.metadata.namespace.as_ref().unwrap());
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
                if reason.clone() == "AlreadyExists" =>
            {
                return Ok(())
            }
            _ => return Err(Error::ReconcileServiceFailed(e)),
        },
        _ => return Ok(()),
    }
}

async fn reconcile_client_service(zk: &ZookeeperCluster, client: Client) -> Result<(), Error> {
    // Create the ZookeeperCluster client service.
    // The client service provides a stable ip and domain name to connect to the client port.
    let svc_api =
        Api::<corev1::Service>::namespaced(client.clone(), zk.metadata.namespace.as_ref().unwrap());
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
                if reason.clone() == "AlreadyExists" =>
            {
                return Ok(())
            }
            _ => return Err(Error::ReconcileServiceFailed(e)),
        },
        _ => return Ok(()),
    }
}

async fn reconcile_admin_server_service(
    zk: &ZookeeperCluster,
    client: Client,
) -> Result<(), Error> {
    // Create the ZookeeperCluster client service.
    // The client service provides a stable ip and domain name to connect to the admin server port.
    let svc_api =
        Api::<corev1::Service>::namespaced(client.clone(), zk.metadata.namespace.as_ref().unwrap());
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
                if reason.clone() == "AlreadyExists" =>
            {
                return Ok(())
            }
            _ => return Err(Error::ReconcileServiceFailed(e)),
        },
        _ => return Ok(()),
    }
}

async fn reconcile_config_map(zk: &ZookeeperCluster, client: Client) -> Result<(), Error> {
    // Reconcile the ZookeeperCluster configmap.
    // The configmap stores the configuration data for zookeeper.
    let cm_api = Api::<corev1::ConfigMap>::namespaced(
        client.clone(),
        zk.metadata.namespace.as_ref().unwrap(),
    );
    let cm = make_configmap(&zk);
    let cm_name = cm.metadata.name.as_ref().unwrap();
    let cm_o = cm_api
        .get_opt(cm_name)
        .await
        .map_err(Error::ReconcileConfigMapFailed)?;

    if cm_o.is_some() {
        info!(
            "Current rv of configmap: {}",
            cm_o.as_ref()
                .unwrap()
                .metadata
                .resource_version
                .as_ref()
                .unwrap()
        );
        info!("Update configmap: {}", cm_name);
        let updated_cm = ConfigMap {
            data: cm.data,
            binary_data: cm.binary_data,
            immutable: cm.immutable,
            ..cm_o.unwrap()
        };
        cm_api
            .replace(cm_name, &PostParams::default(), &updated_cm)
            .await
            .map_err(Error::ReconcileConfigMapFailed)?;
        Ok(())
    } else {
        info!("Create configmap: {}", cm_name);
        cm_api
            .create(&PostParams::default(), &cm)
            .await
            .map_err(Error::ReconcileConfigMapFailed)?;
        Ok(())
    }
}

async fn reconcile_stateful_set(zk: &ZookeeperCluster, client: Client) -> Result<(), Error> {
    // Create the ZookeeperCluster statefulset.
    // The statefulset hosts all the zookeeper pods and volumes.
    let sts_api = Api::<appsv1::StatefulSet>::namespaced(
        client.clone(),
        zk.metadata.namespace.as_ref().unwrap(),
    );
    let sts = make_statefulset(&zk);
    let sts_name = sts.metadata.name.as_ref().unwrap();
    let sts_o = sts_api
        .get_opt(sts_name)
        .await
        .map_err(Error::ReconcileStatefulSetFailed)?;

    if sts_o.is_some() {
        info!(
            "Current rv of statefulset: {}",
            sts_o
                .as_ref()
                .unwrap()
                .metadata
                .resource_version
                .as_ref()
                .unwrap()
        );
        let old_sts = sts_o.unwrap();
        info!("Update statefulset: {}", sts_name);
        let updated_sts = StatefulSet {
            spec: sts.spec,
            ..old_sts
        };

        if updated_sts.spec.as_ref().unwrap().replicas.unwrap()
            < old_sts.spec.as_ref().unwrap().replicas.unwrap()
        {
            // Scale down
            info!("Scale down statefulset: {}", sts_name);

            let cluster = zk.metadata.name.clone().unwrap()
                + "-client."
                + zk.metadata.namespace.as_ref().unwrap()
                + ".svc.cluster.local:2181";
            info!("Connecting to Zookeeper cluster: {}", cluster);
            let client = zk::Client::connect(cluster.as_str(), Duration::from_secs(20))
                .await
                .map_err(Error::ZkClusterConnectFailed)?;

            let (config_bytes, stat, watcher) = client.get_and_watch_config().await.unwrap();

            let input = String::from_utf8(config_bytes).unwrap();
            let num_servers_to_keep = updated_sts.spec.as_ref().unwrap().replicas.unwrap() as usize;

            // split
            let mut servers: Vec<&str> = input.split('\n').collect();
            servers.pop(); // the last one is version, discard

            let kept_servers: Vec<&str> = servers.into_iter().take(num_servers_to_keep).collect();

            // use ',' to join
            let final_config = kept_servers.join(",");

            info!("Modified config: {}", final_config);
            let strings = vec![final_config.as_str()];
            let test_update = EnsembleUpdate::New {
                ensemble: strings.iter().cloned(),
            };
            let result = client.update_ensemble(test_update, Some(-1));
            result.await.map_err(Error::ZkClientCommandFailed)?;
        }
        // Scale up or no change

        sts_api
            .replace(sts_name, &PostParams::default(), &updated_sts)
            .await
            .map_err(Error::ReconcileStatefulSetFailed)?;
        Ok(())
    } else {
        info!("Create statefulset: {}", sts_name);
        sts_api
            .create(&PostParams::default(), &sts)
            .await
            .map_err(Error::ReconcileStatefulSetFailed)?;
        Ok(())
    }
}

async fn reconcile_zk_node(zk: &ZookeeperCluster, client: Client) -> Result<(), Error> {
    // Another way to remove a zk member: pod exec the following
    // java -Dlog4j.configuration=file:/conf/log4j-quiet.properties -jar /opt/libs/zu.jar remove zookeeper-client:2181 id_to_remove
    // or
    // ./zkCli.sh reconfig -remove 2,3
    let sts_api = Api::<appsv1::StatefulSet>::namespaced(
        client.clone(),
        zk.metadata.namespace.as_ref().unwrap(),
    );
    let sts = sts_api
        .get(zk.metadata.name.as_ref().unwrap())
        .await
        .map_err(Error::GetStatefulSetFailed)?;
    if sts.status.is_some()
        && sts.status.clone().unwrap().ready_replicas.is_some()
        && sts.status.unwrap().ready_replicas.unwrap() == zk.spec.replicas
    {
        let path = cluster_size_zk_node_path(zk);
        info!("Try to create {} node since all replicas are ready", path);
        let zk_client = ZooKeeper::connect(
            zk_service_uri(zk).as_str(),
            Duration::from_secs(10),
            LoggingWatcher,
        )
        .map_err(Error::ClusterSizeZKNodeCreationFailed)?;
        match zk_client
            .exists(&path, false)
            .map_err(Error::ClusterSizeZKNodeCreationFailed)?
        {
            Some(_) => Ok(()),
            None => {
                // First create the parent node
                zk_client
                    .create(
                        "/zookeeper-operator",
                        format!("CLUSTER_SIZE={}", zk.spec.replicas)
                            .as_str()
                            .as_bytes()
                            .to_vec(),
                        Acl::open_unsafe().clone(),
                        CreateMode::Persistent,
                    )
                    .map_err(Error::ClusterSizeZKNodeCreationFailed)?;
                zk_client
                    .create(
                        &path,
                        format!("CLUSTER_SIZE={}", zk.spec.replicas)
                            .as_str()
                            .as_bytes()
                            .to_vec(),
                        Acl::open_unsafe().clone(),
                        CreateMode::Persistent,
                    )
                    .map_err(Error::ClusterSizeZKNodeCreationFailed)?;
                Ok(())
            }
        }
    } else {
        Ok(())
    }
}

/// Controller triggers this whenever our main object or our children changed
async fn reconcile(zk_from_cache: Arc<ZookeeperCluster>, ctx: Arc<Data>) -> Result<Action, Error> {
    let client = &ctx.client;

    let zk_name = zk_from_cache
        .metadata
        .name
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.name"))?;
    let zk_ns = zk_from_cache
        .metadata
        .namespace
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.namespace"))?;

    let zk_api = Api::<ZookeeperCluster>::namespaced(client.clone(), &zk_ns);

    // Get the ZookeeperCluster custom resource before taking any reconciliation actions.
    let get_result = zk_api.get(&zk_name).await;
    match get_result {
        Err(kube_client::error::Error::Api(kube_core::ErrorResponse { reason, .. }))
            if &reason == "NotFound" =>
        {
            info!("{} not found, end reconcile", zk_name);
            return Ok(Action::await_change());
        }
        Err(e) => return Err(Error::CRGetFailed(e)),
        _ => {}
    }
    let zk = get_result.unwrap();

    reconcile_headless_service(&zk, client.clone()).await?;
    reconcile_client_service(&zk, client.clone()).await?;
    reconcile_admin_server_service(&zk, client.clone()).await?;
    reconcile_config_map(&zk, client.clone()).await?;
    reconcile_stateful_set(&zk, client.clone()).await?;
    // reconcile_zk_node(&zk, client.clone()).await?;

    Ok(Action::requeue(Duration::from_secs(60)))
}

/// The controller triggers this on reconcile errors
fn error_policy(_object: Arc<ZookeeperCluster>, error: &Error, _ctx: Arc<Data>) -> Action {
    warn!("Reconcile failed due to error: {}", error);
    Action::requeue(Duration::from_secs(10))
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
    } else {
        warn!("wrong command; please use \"export\" or \"run\"");
    }
    Ok(())
}
