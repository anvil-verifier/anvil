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
use deps_hack::VReplicaSet;

// Note from Cody Rivera, 4/17/2025: This test is a copy of vreplicaset_e2e.rs
// for now, but could be expanded.

pub fn v_deployment() -> String {
    "
    apiVersion: anvil.dev/v1
    kind: VDeployment
    metadata:
      name: pause-deployment
      labels:
        app: pause-demo
    spec:
      replicas: 3
      selector:
        matchLabels:
          app: pause-demo
      template:
        metadata:
          labels:
            app: pause-demo
        spec:
          containers:
          - name: pause
            image: k8s.gcr.io/pause:3.9
    "
    .to_string()
}

pub async fn desired_state_test(client: Client, vd_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            error!("Time out on desired state test");
            return Err(Error::Timeout);
        }
        // Check ReplicaSet
        let vrs_api: Api<VReplicaSet> = Api::default_namespaced(client.clone());
        let vrs_list = vrs_api.list(&ListParams::default()).await;
    
        // fail with "404 page not found"
        // we can refer to
        // https://github.com/Arnavion/k8s-openapi/k8s-openapi-tests/src/custom_resource_definition.rs
        // or
        // https://github.com/kube-rs/kube/blob/main/examples/crd_api.rs

        match vrs_list {
            Err(e) => {
                info!("List VReplicaSet failed with error {}.", e);
                continue;
            }
            Ok(vrs_list) => {
                if vrs_list.items.len() == 1 {
                    info!("We have 1 VReplicaSet now.");
                    let rs = vrs_list.items[0].clone();
                    if !(rs.metadata.labels.is_some()
                        && rs.metadata.labels.as_ref().unwrap().get("app").is_some()
                        && rs
                            .metadata
                            .labels
                            .as_ref()
                            .unwrap()
                            .get("app")
                            .unwrap()
                            .clone()
                            == "pause-demo".to_string())
                    {
                        info!("Labels are incorrect; should have app:pause-demo.");
                        return Err(Error::VReplicaSetFailed);
                    } else {
                        info!("We have 1 VReplicaSet now with correct labels.");
                        break;
                    }
                } else {
                    info!("VReplicaSet number is {} which is not 1.", vrs_list.items.len());
                    return Err(Error::VReplicaSetFailed);
                }
            }
        }
    }

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
                            && pod.metadata.labels.as_ref().unwrap().get("app").is_some()
                            && pod
                                .metadata
                                .labels
                                .as_ref()
                                .unwrap()
                                .get("app")
                                .unwrap()
                                .clone()
                                == "pause-demo".to_string())
                        {
                            info!("Labels are incorrect; should have app:pause-demo.");
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

pub async fn scaling_test(client: Client, vd_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(600);
    let mut start = Instant::now();
    let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
    let vrs_api: Api<VReplicaSet> = Api::default_namespaced(client.clone());

    run_command(
        "kubectl",
        vec![
            "patch",
            "vrs",
            "pause",
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

        let vrs_list = vrs_api.list(&ListParams::default()).await;
        // should have 1 old and 1 new VReplicaSet
        match vrs_list {
            Err(e) => {
                info!("List VReplicaSet failed with error {}.", e);
                continue;
            }
            Ok(vrs_list) => {
                if vrs_list.items.len() != 2 {
                    info!(
                        "VReplicaSet number is {} which is not 2.",
                        vrs_list.items.len()
                    );
                    return Err(Error::VReplicaSetFailed);
                }
            }
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
                            && pod.metadata.labels.as_ref().unwrap().get("app").is_some()
                            && pod
                                .metadata
                                .labels
                                .as_ref()
                                .unwrap()
                                .get("app")
                                .unwrap()
                                .clone()
                                == "pause".to_string())
                        {
                            info!("Labels are incorrect; should have tire:pause.");
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
            "vd",
            "pause",
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

        let vrs_list = vrs_api.list(&ListParams::default()).await;
        // should have 2 old and 1 new VReplicaSet
        match vrs_list {
            Err(e) => {
                info!("List VReplicaSet failed with error {}.", e);
                continue;
            }
            Ok(vrs_list) => {
                if vrs_list.items.len() != 3 {
                    info!(
                        "VReplicaSet number is {} which is not 3.",
                        vrs_list.items.len()
                    );
                    return Err(Error::VReplicaSetFailed);
                }
            }
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
                            && pod.metadata.labels.as_ref().unwrap().get("app").is_some()
                            && pod
                                .metadata
                                .labels
                                .as_ref()
                                .unwrap()
                                .get("app")
                                .unwrap()
                                .clone()
                                == "pause".to_string())
                        {
                            info!("Labels are incorrect; should have app:pause.");
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

pub async fn v2_vdeployment_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crd_api: Api<CustomResourceDefinition> = Api::all(client.clone());
    let vrs_crd = crd_api.get("vreplicasets.anvil.dev").await;
    match vrs_crd {
        Err(e) => {
            error!("VReplicaSet CRD not found, create one before run the e2e test.");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            info!("VReplicaSet CRD found, continue to run the e2e test.");
        }
    }
    let vd_crd = crd_api.get("vdeployments.anvil.dev").await;
    match vd_crd {
        Err(e) => {
            error!("VDeployment CRD not found, create one before run the e2e test.");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            info!("VDeployment CRD found, continue to run the e2e test.");
        }
    }

    let discovery = Discovery::new(client.clone()).run().await?;
    let vd_name = apply(v_deployment(), client.clone(), &discovery).await?;

    desired_state_test(client.clone(), vd_name.clone()).await?;
    scaling_test(client.clone(), vd_name.clone()).await?;

    info!("E2e test passed.");
    Ok(())
}