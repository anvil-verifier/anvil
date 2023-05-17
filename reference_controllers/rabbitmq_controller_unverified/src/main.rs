#![allow(clippy::unnecessary_lazy_evaluations)]


pub mod rabbitmqcluster_types;
pub mod rabbitmqcluster_status;
pub mod headless_service;
pub mod service;
pub mod erlang_cookie;
pub mod default_user_secret;
pub mod rabbitmq_plugin_configmap;
pub mod service_configmap;
pub mod service_account;
pub mod role;
pub mod role_binding;
pub mod statefulset;

use anyhow::Result;
use futures::StreamExt;
use k8s_openapi::api::apps::v1 as appsv1;
use k8s_openapi::api::core::v1 as corev1;
use kube::{
    api::{Api, ListParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_client::{self, client};
use kube_core;
use core::time;
use std::{env, sync::Arc};
use thiserror::Error;
use tokio::time::Duration;
use tracing::*;

use crate::rabbitmqcluster_types::*;

#[derive(Debug, Error)]
enum Error {
    #[error("MissingObjectKey: {0}")]
    MissingObjectKey(&'static str),
    #[error("ReplaceImageFail: {0}")]
    ReplaceImageFail(kube_client::Error),
}


struct RabbitmqClusterReconciler {
    client: Client,
    // scheme: kube::runtime::Scheme, can not find same in rust
    Namespace: String,
}

impl RabbitmqClusterReconciler {

}


async fn reconcile(rabbitmq: Arc<RabbitmqCluster>, _ctx: Arc<RabbitmqClusterReconciler>) -> Result<Action, Error> {
    let client = _ctx.client.clone();
    let namespace = _ctx.Namespace.clone();
    let name = rabbitmq
        .metadata
        .name
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.name"))?;
    

    let (duration, err) = reconcile_operator_defaults(&rabbitmq, client).await;
    if duration.as_secs() != 0 || err.is_some() {
        return Ok(Action::requeue(duration));
    }


    info!("Start reconciling");



    let secvice = service::service_build(&rabbitmq);





    Ok(Action::requeue(Duration::from_secs(300)))
}



async fn reconcile_operator_defaults(rabbitmq: &RabbitmqCluster, client: Client) ->  (Duration, Option<Error>){
    let rabbitmq_api: Api<RabbitmqCluster> = Api::namespaced(client, &rabbitmq.metadata.namespace.as_ref().unwrap());
    let mut rabbitmq_replace = rabbitmq.clone();
    if rabbitmq.spec.image.is_none() || rabbitmq.spec.image.as_ref().unwrap() == ""{
        rabbitmq_replace.spec.image = Some(String::from("rabbitmq:3.11.10-management"));
        match rabbitmq_api
              .replace(&rabbitmq.metadata.name.as_ref().unwrap(), &PostParams::default(), &rabbitmq_replace).await
        {
            Err(e) => {
                return (Duration::from_secs(2),Some(Error::ReplaceImageFail(e)))
            },
            Ok(_) => {
                info!("Updated default image");
            }
        };
    }
    (Duration::from_secs(0), None)

    // if rabbitmq.spec.image_pull_secrets.is_none() || rabbitmq.spec.image_pull_secrets.as_ref().unwrap().len() == 0{
    //     let mut rabbitmq_replace = rabbitmq.clone();
    //     rabbitmq_replace.spec.image_pull_secrets = Some(vec![corev1::LocalObjectReference{
    //         name: Some(String::from("regcred")),
    //     }]);
    //     rabbitmq_api.replace(&rabbitmq.metadata.name.as_ref().unwrap(), &PostParams::default(), &rabbitmq_replace);
    // }

    // User default updater image

}



/// object that caused the failure and the actual error
fn error_policy(obj: Arc<RabbitmqCluster>, _error: &Error, _ctx: Arc<RabbitmqClusterReconciler>) -> Action {
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
            .run(reconcile, error_policy, Arc::new(RabbitmqClusterReconciler { client: client, Namespace: String::from("rabbitmq-system") }))
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
