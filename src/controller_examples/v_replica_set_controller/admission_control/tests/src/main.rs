#![allow(unused_imports)]
#![allow(unused_variables)]
use k8s_openapi::api::core::v1::{Pod, Service, ServiceAccount};
use k8s_openapi::api::rbac::v1::RoleBinding;
use k8s_openapi::api::{apps::v1::DaemonSet, rbac::v1::Role, apps::v1::ReplicaSet};
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
use std::fs;
pub mod common;
use common::Error;

#[tokio::main]
async fn main()-> Result<(), Error>{
    tracing_subscriber::fmt::init();
    let client = Client::try_default().await?;

    // Replace when using manifests for custom CRD

    // let crd_api: Api<CustomResourceDefinition> = Api::all(client.clone());
    // let vrs_crd = crd_api.get("vreplicasets.anvil.dev").await;
    // match vrs_crd {
    //     Err(e) => {
    //         error!("No CRD found, create one before run the e2e test.");
    //         return Err(Error::CRDGetFailed(e));
    //     }
    //     Ok(crd) => {
    //         info!("CRD found, continue to run the e2e test.");
    //     }
    // }

    let replicasets_api: Api<ReplicaSet> = Api::namespaced(client.clone(), "default");

    let replicasets = replicasets_api.list(&Default::default()).await;

    match replicasets {
        Ok(list) => {
            info!("Successfully retrieved ReplicaSets");
        }
        Err(e) => {
            error!("Failed to list ReplicaSets");
            return Err(Error::ReplicaSetListFailed);
        }
    }

    // contains test cases
    let manifest_dir = "../manifests/replicaset";
    let paths = fs::read_dir(manifest_dir).unwrap();

    for path in paths {
        let path = path.unwrap().path();

        // check if given manifest should pass or not (signified by "ok" at beginning of file)
        let file_name = path.file_name();
        let valid_manifest = file_name.map_or(false, |name| name.to_str().map_or(false, |s| s.starts_with("ok")));

        if path.extension().map_or(false, |e| e == "yaml" || e == "yml") {
            let manifest_content = fs::read_to_string(&path).unwrap();
            info!("Processing manifest: {:?}", path);

            let manifest: ReplicaSet = serde_yaml::from_str(&manifest_content).unwrap();

            // apply manifest
            let apply_result = replicasets_api.create(&PostParams::default(), &manifest).await;
            match apply_result {
                Ok(created_replicaset) => {
                    if valid_manifest {
                        info!("Manifest from {} successfully created", path.display());
                    }
                    else {
                        error!("Manifest from {} created ReplicaSet when it should not have", path.display());
                    }
                }
                Err(e) => {
                    if valid_manifest {
                        error!("Manifest from {} failed to create ReplicaSet when it should have been successful. {}", path.display(), e);
                    }
                    else {
                        info!("Manifest from {} correctly failed to create ReplicaSet", path.display());
                    }
                }
            }
        }
    }

    Ok(())
}