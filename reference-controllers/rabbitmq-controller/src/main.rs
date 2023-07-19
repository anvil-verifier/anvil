#![allow(clippy::unnecessary_lazy_evaluations)]

pub mod default_user_secret;
pub mod erlang_cookie_secret;
pub mod headless_service;
pub mod rabbitmq_plugins;
pub mod rabbitmqcluster_types;
pub mod role;
pub mod role_binding;
pub mod server_configmap;
pub mod service;
pub mod service_account;
pub mod statefulset;

use crate::rabbitmqcluster_types::*;
use anyhow::Result;
use futures::StreamExt;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::api::rbac::v1 as rbacv1;
use k8s_openapi::api::{apps::v1 as appsv1, apps::v1::StatefulSet, core::v1::ConfigMap};
use kube::{
    api::{
        Api, ApiResource, DynamicObject, GroupVersionKind, ListParams, Patch, PatchParams,
        PostParams,
    },
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_core::{self, ResourceExt};
use serde_json::json;
use std::{env, sync::Arc};
use thiserror::Error;
use tokio::time::Duration;
use tracing::*;

#[derive(Debug, Error)]
enum Error {
    // #[error("Failed to get CR: {0}")]
    // CRGetFailed(#[source] kube::Error),
    #[error("Failed to create ConfigMap: {0}")]
    ConfigMapCreationFailed(#[source] kube::Error),

    #[error("Failed to create Service: {0}")]
    ServiceCreationFailed(#[source] kube::Error),
    #[error("Failed to create ServiceAccount: {0}")]
    ServiceAccountCreationFailed(#[source] kube::Error),

    #[error("Failed to create Role: {0}")]
    RoleCreationFailed(#[source] kube::Error),
    #[error("Failed to create RoleBinding: {0}")]
    RoleBindingCreationFailed(#[source] kube::Error),

    #[error("Failed to reconcile StatefulSet: {0}")]
    ReconcileStatefulSetFailed(#[source] kube::Error),

    #[error("Failed to reconcile ConfigMap: {0}")]
    ReconcileConfigMapFailed(#[source] kube::Error),

    #[error("Failed to update annotation: {0}")]
    AnnotationUpdateFailed(#[source] kube::Error),

    #[error("Failed to restart sts: {0}")]
    RestartStatefulSetFailed(#[source] kube::Error),
}

struct Data {
    client: Client,
}

async fn reconcile_stateful_set(rabbitmq: &RabbitmqCluster, client: &Client) -> Result<(), Error> {
    // Create the RabbitmqCluster statefulset.
    // The statefulset hosts all the Rabbitmq pods and volumes.
    let sts_api = Api::<appsv1::StatefulSet>::namespaced(
        client.clone(),
        rabbitmq.metadata.namespace.as_ref().unwrap(),
    );
    let sts = statefulset::statefulset_build(&rabbitmq);
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

        let mut updated_sts = StatefulSet {
            spec: sts.spec,
            ..old_sts.clone()
        };
        // restore the old template annotations
        updated_sts
            .spec
            .as_mut()
            .unwrap()
            .template
            .metadata
            .as_mut()
            .unwrap()
            .annotations = old_sts
            .spec
            .as_ref()
            .unwrap()
            .template
            .metadata
            .as_ref()
            .unwrap()
            .annotations
            .clone();
        if updated_sts.spec.as_ref().unwrap().replicas.unwrap()
            >= old_sts.spec.as_ref().unwrap().replicas.unwrap()
        {
            // Only scale up is supported.
            info!("Update statefulset: {}", sts_name);
            sts_api
                .replace(sts_name, &PostParams::default(), &updated_sts)
                .await
                .map_err(Error::ReconcileStatefulSetFailed)?;
        }
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

async fn reconcile_server_config_map(
    rabbitmq: &RabbitmqCluster,
    client: &Client,
) -> Result<(), Error> {
    // Reconcile the RabbitmqCluster server configmap.
    let cm_api = Api::<corev1::ConfigMap>::namespaced(
        client.clone(),
        rabbitmq.metadata.namespace.as_ref().unwrap(),
    );
    let server_config = server_configmap::server_configmap_build(&rabbitmq);
    let server_config_name = server_config.metadata.name.as_ref().unwrap();
    let server_config_o = cm_api
        .get_opt(server_config_name)
        .await
        .map_err(Error::ReconcileConfigMapFailed)?;

    if server_config_o.is_some() {
        let resrouce_version = server_config_o
            .as_ref()
            .unwrap()
            .metadata
            .resource_version
            .as_ref()
            .unwrap()
            .clone();
        info!("Current rv of server configmap: {}", resrouce_version);
        if server_config.data != server_config_o.as_ref().unwrap().data {
            // If the data is different, update the server config
            info!("Update configmap: {}", server_config_name);
            let updated_server_config = ConfigMap {
                data: server_config.data,
                binary_data: server_config.binary_data,
                immutable: server_config.immutable,
                ..server_config_o.unwrap()
            };
            cm_api
                .replace(
                    server_config_name,
                    &PostParams::default(),
                    &updated_server_config,
                )
                .await
                .map_err(Error::ReconcileConfigMapFailed)?;

            let gvk = GroupVersionKind::gvk("", "v1", "ConfigMap");
            let api_resource = ApiResource::from_gvk(&gvk);
            update_annotation(
                api_resource,
                rabbitmq.metadata.namespace.as_ref().unwrap(),
                &server_config_name,
                "lastVersion",
                &resrouce_version,
                &client,
            )
            .await?;
        }
        Ok(())
    } else {
        info!("Create configmap: {}", server_config_name);
        cm_api
            .create(&PostParams::default(), &server_config)
            .await
            .map_err(Error::ReconcileConfigMapFailed)?;
        Ok(())
    }
}

async fn restart_sts_if_needed(rabbitmq: &RabbitmqCluster, client: &Client) -> Result<(), Error> {
    // Restart the statefulset if the server configmap is newer than the sts.
    let cm_api = Api::<corev1::ConfigMap>::namespaced(
        client.clone(),
        rabbitmq.metadata.namespace.as_ref().unwrap(),
    );
    let server_config = server_configmap::server_configmap_build(&rabbitmq);
    let server_config_name = server_config.metadata.name.as_ref().unwrap();
    let server_config_o = cm_api
        .get_opt(server_config_name)
        .await
        .map_err(Error::ReconcileConfigMapFailed)?;

    let sts_api = Api::<appsv1::StatefulSet>::namespaced(
        client.clone(),
        rabbitmq.metadata.namespace.as_ref().unwrap(),
    );
    let sts = statefulset::statefulset_build(&rabbitmq);
    let sts_name = sts.metadata.name.as_ref().unwrap();
    let sts_o = sts_api
        .get_opt(sts_name)
        .await
        .map_err(Error::ReconcileStatefulSetFailed)?;

    let server_config_last_version = match server_config_o.clone().unwrap().metadata.annotations {
        Some(annotations) => annotations.get("lastVersion").cloned(),
        None => None,
    };

    if !server_config_last_version.is_some() {
        // If lastVersion is not set, it means the server configmap is not updated.
        // If the server configmap is not updated, return.
        return Ok(());
    }

    let sts_restartedat = match sts_o
        .clone()
        .unwrap()
        .spec
        .unwrap()
        .template
        .metadata
        .unwrap()
        .annotations
    {
        Some(annotations) => annotations.get("restartedVersion").cloned(),
        None => None,
    };

    let server_config_updatedat = server_config_o
        .as_ref()
        .unwrap()
        .metadata
        .resource_version
        .clone();
    if sts_restartedat.is_some()
        && sts_restartedat.clone().unwrap() >= server_config_updatedat.clone().unwrap()
    {
        // sts was updated after the last server-conf configmap update; no need to restart sts
        return Ok(());
    }

    // Restart the sts by changing the pod template.
    let patch = Patch::Merge(json!({
        "spec": {
            "template": {
                "metadata": {
                    "annotations": {
                        "restartedVersion": server_config_o.unwrap().metadata.resource_version.unwrap(),
                    },
                },
            },
        },
    }));

    let pp = PatchParams::default();

    sts_api
        .patch(sts_name, &pp, &patch)
        .await
        .map_err(Error::RestartStatefulSetFailed)?;
    info!("Restart statefulset: {}", sts_name);
    Ok(())
}

async fn reconcile(rabbitmq: Arc<RabbitmqCluster>, _ctx: Arc<Data>) -> Result<Action, Error> {
    let client = &_ctx.client;
    let namespace = rabbitmq.namespace().unwrap();

    info!("Reconcile operator defaults done, get APIs");
    let svc_api = Api::<corev1::Service>::namespaced(client.clone(), &namespace);
    info!("Get service API");
    let svc_acc_api = Api::<corev1::ServiceAccount>::namespaced(client.clone(), &namespace);
    info!("Get service account API");
    let cm_api = Api::<corev1::ConfigMap>::namespaced(client.clone(), &namespace);
    let secret_api = Api::<corev1::Secret>::namespaced(client.clone(), &namespace);
    let role_api = Api::<rbacv1::Role>::namespaced(client.clone(), &namespace);
    let role_binding_api = Api::<rbacv1::RoleBinding>::namespaced(client.clone(), &namespace);

    info!("Start reconciling");

    // Create headless service
    let headless_service = headless_service::headless_build(&rabbitmq);
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

    // Create service
    let service = service::service_build(&rabbitmq);
    info!(
        "Create service: {}",
        service.metadata.name.as_ref().unwrap()
    );
    match svc_api.create(&PostParams::default(), &service).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ServiceCreationFailed(e)),
        },
        _ => {}
    }

    // Create erlang cookie
    let erlang_cookie_secret = erlang_cookie_secret::erlang_build(&rabbitmq);
    info!(
        "Create erlang cookie: {}",
        erlang_cookie_secret.metadata.name.as_ref().unwrap()
    );
    match secret_api
        .create(&PostParams::default(), &erlang_cookie_secret)
        .await
    {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ServiceCreationFailed(e)),
        },
        _ => {}
    }

    // Create default user secret
    let default_user_secret = default_user_secret::default_user_secret_build(&rabbitmq);
    info!(
        "Create user secret: {}",
        default_user_secret.metadata.name.as_ref().unwrap()
    );
    match secret_api
        .create(&PostParams::default(), &default_user_secret)
        .await
    {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ServiceCreationFailed(e)),
        },
        _ => {}
    }

    // Create plugins config
    let plugins_config = rabbitmq_plugins::plugins_configmap_build(&rabbitmq);
    info!(
        "Create plugins config: {}",
        plugins_config.metadata.name.as_ref().unwrap()
    );
    match cm_api.create(&PostParams::default(), &plugins_config).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ConfigMapCreationFailed(e)),
        },
        _ => {}
    }

    // Create sever config
    reconcile_server_config_map(&rabbitmq, &client).await?;

    // Create service account
    let service_account = service_account::service_account_build(&rabbitmq);
    info!(
        "Create service account: {}",
        service_account.metadata.name.as_ref().unwrap()
    );
    match svc_acc_api
        .create(&PostParams::default(), &service_account)
        .await
    {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ServiceAccountCreationFailed(e)),
        },
        _ => {}
    }

    // Create role
    let role = role::role_build(&rabbitmq);
    info!("Create role: {}", role.metadata.name.as_ref().unwrap());
    match role_api.create(&PostParams::default(), &role).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::RoleCreationFailed(e)),
        },
        _ => {}
    }

    // Create role binding
    let role_binding = role_binding::role_binding_build(&rabbitmq);
    info!(
        "Create role binding: {}",
        role_binding.metadata.name.as_ref().unwrap()
    );
    match role_binding_api
        .create(&PostParams::default(), &role_binding)
        .await
    {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::RoleBindingCreationFailed(e)),
        },
        _ => {}
    }

    // Reconcile statefulset
    reconcile_stateful_set(&rabbitmq, &client).await?;

    // Check if restart is needed
    restart_sts_if_needed(&rabbitmq, &client).await?;

    Ok(Action::requeue(Duration::from_secs(300)))
}

/// object that caused the failure and the actual error
fn error_policy(_obj: Arc<RabbitmqCluster>, _error: &Error, _ctx: Arc<Data>) -> Action {
    Action::requeue(Duration::from_secs(60))
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();

    if cmd == String::from("export") {
        info!("exporting custom resource definition");
        println!("{}", serde_yaml::to_string(&RabbitmqCluster::crd())?);
        Ok(())
    } else if cmd == String::from("run") {
        info!("running rabbitmq-controller");
        let client = Client::try_default().await?;
        let rabbitmq = Api::<RabbitmqCluster>::all(client.clone());

        Controller::new(rabbitmq, ListParams::default())
            .shutdown_on_signal()
            .run(reconcile, error_policy, Arc::new(Data { client: client }))
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

async fn update_annotation(
    api_resoruce: ApiResource,
    namespace: &str,
    obj_name: &str,
    key: &str,
    value: &str,
    client: &Client,
) -> Result<(), Error> {
    let api: Api<DynamicObject> = Api::namespaced_with(client.clone(), namespace, &api_resoruce);
    info!(
        "Fetching DynamicObject: {}, Its type{:?}",
        obj_name, api_resoruce
    );
    let mut obj = api
        .get(obj_name)
        .await
        .map_err(Error::AnnotationUpdateFailed)?;
    info!(
        "Fetched DynamicObject, Updating annotation: {}={}",
        key, value
    );
    let mut annotations = obj.metadata.annotations.unwrap_or_default();
    annotations.insert(key.to_string(), value.to_string());
    obj.metadata.annotations = Some(annotations);

    let pp = PostParams::default();
    api.replace(obj_name, &pp, &obj)
        .await
        .map_err(Error::AnnotationUpdateFailed)?;
    Ok(())
}
