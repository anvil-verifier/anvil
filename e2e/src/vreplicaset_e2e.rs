#![allow(unused_imports)]
#![allow(unused_variables)]
use k8s_openapi::api::core::v1::{Pod, Service, ServiceAccount};
use k8s_openapi::api::rbac::v1::RoleBinding;
use k8s_openapi::api::{apps::v1::DaemonSet, rbac::v1::Role};
use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition;
use kube::{
    api::{
        Api, AttachParams, AttachedProcess, DeleteParams, ListParams, Patch, PatchParams,
        PostParams, ResourceExt,
    },
    core::crd::CustomResourceExt,
    discovery::{ApiCapabilities, ApiResource, Discovery, Scope},
    Client, CustomResource,
};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::path::PathBuf;
use std::thread;
use std::time::{Duration, Instant};
use tokio::time::sleep;
use tracing::*;

use crate::common::*;

// Note from Cody Rivera, 4/17/2025: This test is a copy of vreplicaset_e2e.rs
// for now, but could be expanded.

pub fn v_replica_set() -> String {
    "
    apiVersion: anvil.dev/v1
    kind: VReplicaSet
    metadata:
      name: frontend
      labels:
        app: guestbook
        tier: frontend
    spec:
      replicas: 3
      selector:
        matchLabels:
          tier: frontend
      template:
        metadata:
          labels:
            tier: frontend
        spec:
          containers:
          - name: php-redis
            image: us-docker.pkg.dev/google-samples/containers/gke/gb-frontend:v5
    "
    .to_string()
}

pub async fn desired_state_test(client: Client, vrs_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            error!("Time out on desired state test");
            return Err(Error::Timeout);
        }
        // Check pods
        let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
        let pods = pod_api.list(&ListParams::default()).await;
        match pods {
            Err(e) => {
                info!("List pods failed with error {}.", e);
                continue;
            }
            Ok(pods) => {
                if pods.items.len() < 3 {
                    info!(
                        "Pod number is {} which is smaller than 3; still creating.",
                        pods.items.len()
                    );
                    continue;
                } else if pods.items.len() > 3 {
                    info!("Pod number is {} which is larger than 3.", pods.items.len());
                    return Err(Error::VReplicaSetFailed);
                } else {
                    info!("We have 3 pods now.");
                    for pod in pods.items.iter() {
                        if !(pod.metadata.labels.is_some()
                            && pod.metadata.labels.as_ref().unwrap().get("tier").is_some()
                            && pod
                                .metadata
                                .labels
                                .as_ref()
                                .unwrap()
                                .get("tier")
                                .unwrap()
                                .clone()
                                == "frontend".to_string())
                        {
                            info!("Labels are incorrect; should have tier:frontend.");
                            return Err(Error::VReplicaSetFailed);
                        }
                    }
                    break;
                }
            }
        }
    }
    info!("Desired state test passed.");
    Ok(())
}

pub async fn scaling_test(client: Client, vrs_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(600);
    let mut start = Instant::now();
    let pod_api: Api<Pod> = Api::default_namespaced(client.clone());

    run_command(
        "kubectl",
        vec![
            "patch",
            "vrs",
            "frontend",
            "--type=json",
            "-p",
            "[{\"op\": \"replace\", \"path\": \"/spec/replicas\", \"value\": 5}]",
        ],
        "failed to scale VReplicaSet",
    );

    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            error!("Time out on scaling test");
            return Err(Error::Timeout);
        }

        let pods = pod_api.list(&ListParams::default()).await;
        let desired_replicas = 5;
        match pods {
            Err(e) => {
                info!("List pods failed with error {}.", e);
                continue;
            }
            Ok(pods) => {
                if pods.items.len() < desired_replicas {
                    info!(
                        "Pod number is {} which is smaller than 5; still scaling up.",
                        pods.items.len()
                    );
                    continue;
                } else if pods.items.len() > desired_replicas {
                    info!("Pod number is {} which is larger than 5.", pods.items.len());
                    return Err(Error::VReplicaSetFailed);
                } else {
                    info!("We have 5 pods now.");
                    for pod in pods.items.iter() {
                        if !(pod.metadata.labels.is_some()
                            && pod.metadata.labels.as_ref().unwrap().get("tier").is_some()
                            && pod
                                .metadata
                                .labels
                                .as_ref()
                                .unwrap()
                                .get("tier")
                                .unwrap()
                                .clone()
                                == "frontend".to_string())
                        {
                            info!("Labels are incorrect; should have tier:frontend.");
                            return Err(Error::VReplicaSetFailed);
                        }
                    }
                    break;
                }
            }
        }
    }

    start = Instant::now();
    run_command(
        "kubectl",
        vec![
            "patch",
            "vrs",
            "frontend",
            "--type=json",
            "-p",
            "[{\"op\": \"replace\", \"path\": \"/spec/replicas\", \"value\": 3}]",
        ],
        "failed to scale VReplicaSet",
    );

    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            error!("Time out on scaling test");
            return Err(Error::Timeout);
        }

        let pods = pod_api.list(&ListParams::default()).await;
        let desired_replicas = 3;
        match pods {
            Err(e) => {
                info!("List pods failed with error {}.", e);
                continue;
            }
            Ok(pods) => {
                if pods.items.len() > desired_replicas {
                    info!(
                        "Pod number is {} which is larger than 3; still scaling down.",
                        pods.items.len()
                    );
                    continue;
                } else if pods.items.len() < desired_replicas {
                    info!(
                        "Pod number is {} which is smaller than 3.",
                        pods.items.len()
                    );
                    return Err(Error::VReplicaSetFailed);
                } else {
                    info!("We have 3 pods now.");
                    for pod in pods.items.iter() {
                        if !(pod.metadata.labels.is_some()
                            && pod.metadata.labels.as_ref().unwrap().get("tier").is_some()
                            && pod
                                .metadata
                                .labels
                                .as_ref()
                                .unwrap()
                                .get("tier")
                                .unwrap()
                                .clone()
                                == "frontend".to_string())
                        {
                            info!("Labels are incorrect; should have tier:frontend.");
                            return Err(Error::VReplicaSetFailed);
                        }
                    }
                    break;
                }
            }
        }
    }

    info!("Scaling test passed.");
    Ok(())
}

pub async fn vreplicaset_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crd_api: Api<CustomResourceDefinition> = Api::all(client.clone());
    let vrs_crd = crd_api.get("vreplicasets.anvil.dev").await;
    match vrs_crd {
        Err(e) => {
            error!("No CRD found, create one before run the e2e test.");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            info!("CRD found, continue to run the e2e test.");
        }
    }

    let discovery = Discovery::new(client.clone()).run().await?;
    let vrs_name = apply(v_replica_set(), client.clone(), &discovery).await?;

    desired_state_test(client.clone(), vrs_name.clone()).await?;
    scaling_test(client.clone(), vrs_name.clone()).await?;

    info!("E2e test passed.");
    Ok(())
}
