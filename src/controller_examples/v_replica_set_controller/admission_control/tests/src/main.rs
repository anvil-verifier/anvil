#![allow(unused_variables)]
use k8s_openapi::api::apps::v1::ReplicaSet;
use kube::{
    api::{Api, PostParams},
    Client
};
use tracing::*;
use std::fs;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Failed to get kube client: {0}")]
    ClientGetFailed(#[from] kube_client::Error),

    #[error("Failed to apply yaml file!")]
    ApplyFailed,

    #[error("Failed to parse the yaml file!")]
    ParseYamlFailed(#[from] serde_yaml::Error),

    #[error("Failed to parse the json format!")]
    ParseJsonFailed(#[from] serde_json::Error),

    #[error("Failed to find the yaml file in provided path!")]
    GVKFailed(#[from] std::io::Error),

    #[error("Failed to get CRD: {0}")]
    CRDGetFailed(#[source] kube::Error),

    #[error("ReplicaSet list generation failed!")]
    ReplicaSetListFailed,

    #[error("ReplicaSet creation failed!")]
    ReplicaSetCreationFailed,

    #[error("Valid ReplicaSet failed admission!")]
    ReplicaSetValidAdmissionFailed,

    #[error("Invalid ReplicaSet passed admission!")]
    ReplicaSetInvalidAdmissionPassed,
}

#[tokio::main]
async fn main()-> Result<(), Error>{
    tracing_subscriber::fmt::init();
    let client = Client::try_default().await?;

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
            info!("Manifest: {:?}", manifest);
            // apply manifest
            let apply_result = replicasets_api.create(&PostParams::default(), &manifest).await;
            match apply_result {
                Ok(created_replicaset) => {
                    if valid_manifest {
                        info!("Manifest from {} successfully created", path.display());
                    }
                    else {
                        error!("Manifest from {} created ReplicaSet when it should not have", path.display());
                        return Err(Error::ReplicaSetInvalidAdmissionPassed);
                    }
                }
                Err(e) => {
                    if valid_manifest {
                        error!("Manifest from {} failed to create ReplicaSet when it should have been successful. {}", path.display(), e);
                        return Err(Error::ReplicaSetValidAdmissionFailed);
                    }
                    else {
                        info!("Manifest from {} correctly failed to create ReplicaSet", path.display());
                    }
                }
            }
        }
    }
    info!("All tests passed");
    Ok(())
}