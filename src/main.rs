// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

use anyhow::Result;
use futures::StreamExt;
use k8s_openapi::api::core::v1::ConfigMap;
use kube::{
    api::{Api, ListParams, ObjectMeta, PostParams, Resource},
    runtime::controller::{Action, Controller},
    Client,
};
use std::{collections::HashMap, io::BufRead, sync::Arc};
use thiserror::Error;
use tokio::time::Duration;
use tracing::*;

mod crd;
use crd::*;

mod logic;
use logic::*;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Failed to create ConfigMap: {0}")]
    ConfigMapCreationFailed(#[source] kube::Error),
    #[error("Failed to get ConfigMap: {0}")]
    ConfigMapGetFailed(#[source] kube::Error),
}

fn translate_configmapl_to_configmap(
    generator: Arc<ConfigMapGenerator>,
    configmapl: ConfigMapL,
) -> ConfigMap {
    let oref = generator.controller_owner_ref(&()).unwrap();
    ConfigMap {
        metadata: ObjectMeta {
            name: configmapl.name,
            namespace: configmapl.namespace,
            owner_references: Some(vec![oref.clone()]),
            ..ObjectMeta::default()
        },
        data: configmapl.data,
        ..Default::default()
    }
}

fn translate_configmap_to_configmapl(configmap: ConfigMap) -> ConfigMapL {
    ConfigMapL {
        name: configmap.metadata.name,
        namespace: configmap.metadata.namespace,
        data: configmap.data,
    }
}

// Controller triggers this whenever the CR object or configmap object belonging to the cr changes
// Note that the reconcile function is not complete yet
// For now, it does very simple job
// When the CR object is created/updated, the reconcile will create two configmaps with the content
async fn reconcile(generator: Arc<ConfigMapGenerator>, ctx: Arc<Data>) -> Result<Action, Error> {
    let mut current_controller_state = ControllerState::Init;
    let mut current_cluster_state: ClusterState = ClusterState {
        configmaps: HashMap::new(),
    };
    let mut current_api_op_response = APIOpResponse { success: true };

    loop {
        info!("current controller state {:?}", current_controller_state);
        if current_controller_state == ControllerState::Done {
            return Ok(Action::requeue(Duration::from_secs(300)));
        } else if current_controller_state == ControllerState::Retry {
            return Ok(Action::requeue(Duration::from_secs(3)));
        }
        let (next_controller_state, api_op_request) = controller_logic(
            &current_controller_state,
            &current_cluster_state,
            &current_api_op_response,
        );
        current_controller_state = next_controller_state;
        match api_op_request.api_op {
            APIOp::Noop => current_api_op_response.success = true,
            APIOp::GetConfigMap { name, namespace } => {
                let get_result = Api::<ConfigMap>::namespaced(ctx.client.clone(), &namespace)
                    .get_opt(&name)
                    .await
                    .map_err(Error::ConfigMapGetFailed);
                match get_result {
                    Err(_) => current_api_op_response.success = false,
                    Ok(o) => match o {
                        Some(c) => {
                            current_api_op_response.success = true;
                            current_cluster_state.configmaps.insert(
                                format!("{}/{}", namespace, name),
                                Some(translate_configmap_to_configmapl(c)),
                            );
                        }
                        None => {
                            current_api_op_response.success = true;
                            current_cluster_state
                                .configmaps
                                .insert(format!("{}/{}", namespace, name), None);
                        }
                    },
                }
            }
            APIOp::CreateConfigMap {
                name,
                namespace,
                configmapl,
            } => {
                let configmap = translate_configmapl_to_configmap(generator.clone(), configmapl);
                let create_result = Api::<ConfigMap>::namespaced(ctx.client.clone(), &namespace)
                    .create(&PostParams::default(), &configmap)
                    .await
                    .map_err(Error::ConfigMapCreationFailed);
                match create_result {
                    Err(_) => current_api_op_response.success = false,
                    Ok(c) => {
                        current_api_op_response.success = true;
                        current_cluster_state.configmaps.insert(
                            format!("{}/{}", namespace, name),
                            Some(translate_configmap_to_configmapl(c)),
                        );
                    }
                }
            }
        }
    }
}

// The controller triggers this on reconcile errors
fn error_policy(_error: &Error, _ctx: Arc<Data>) -> Action {
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

    let cmgs = Api::<ConfigMapGenerator>::all(client.clone());
    let cms = Api::<ConfigMap>::all(client.clone());

    info!("starting configmapgen-controller");
    info!("press <enter> to force a reconciliation of all objects");

    let (mut reload_tx, reload_rx) = futures::channel::mpsc::channel(0);
    // Using a regular background thread since tokio::io::stdin() doesn't allow aborting reads,
    // and its worker prevents the Tokio runtime from shutting down.
    std::thread::spawn(move || {
        for _ in std::io::BufReader::new(std::io::stdin()).lines() {
            let _ = reload_tx.try_send(());
        }
    });

    Controller::new(cmgs, ListParams::default())
        .owns(cms, ListParams::default())
        .reconcile_all_on(reload_rx.map(|_| ()))
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
