#![allow(clippy::unnecessary_lazy_evaluations)]
#![allow(unused_imports)]

pub mod default_user_secret;
pub mod erlang_cookie_secret;
pub mod headless_service;
pub mod rabbitmq_plugins;
pub mod rabbitmqcluster_status;
pub mod rabbitmqcluster_types;
pub mod role;
pub mod role_binding;
pub mod server_configmap;
pub mod service;
pub mod service_account;
pub mod statefulset;

use anyhow::Result;
use core::time;
use futures::StreamExt;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::api::rbac::v1 as rbacv1;
use k8s_openapi::api::{apps::v1 as appsv1, core::v1::Service};
use kube::{
    api::{Api, ListParams, PostParams},
    client::ConfigExt,
    runtime::controller::{Action, Controller},
    Client, Config, CustomResourceExt,
};
use kube_client::{self, client};
use kube_core::{self, ResourceExt};
use std::str::FromStr;
use std::{env, sync::Arc};
use thiserror::Error;
use tokio::time::Duration;
use tracing::*;

use crate::rabbitmqcluster_types::*;

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

    #[error("Failed to create StatefulSet: {0}")]
    StatefulSetCreationFailed(#[source] kube::Error),
}

struct Data {
    client: Client,
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
    let sts_api = Api::<appsv1::StatefulSet>::namespaced(client.clone(), &namespace);
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
    let server_config = server_configmap::server_configmap_build(&rabbitmq);
    info!(
        "Create server config: {}",
        server_config.metadata.name.as_ref().unwrap()
    );
    match cm_api.create(&PostParams::default(), &server_config).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::ConfigMapCreationFailed(e)),
        },
        _ => {}
    }

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

    // Create statefulset
    let statefulset = statefulset::statefulset_build(&rabbitmq);
    info!(
        "Create statefulset: {}",
        statefulset.metadata.name.as_ref().unwrap()
    );
    match sts_api.create(&PostParams::default(), &statefulset).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" => {}
            _ => return Err(Error::StatefulSetCreationFailed(e)),
        },
        _ => {}
    }

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
        info!("running zookeeper-controller");
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
