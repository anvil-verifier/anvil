#![allow(unused_imports)]
#![allow(unused_variables)]
use kube::{
    api::Api,
    Client,
    discovery::Discovery,
};
use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition;
use tracing::*;
use std::fs;

mod common;
use crate::common::*;

#[tokio::main]
async fn main()-> Result<(), Error>{
    tracing_subscriber::fmt::init();
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

    let replicasets = crd_api.list(&Default::default()).await;

    match replicasets {
        Ok(list) => {
            info!("Successfully retrieved VReplicaSets");
        }
        Err(e) => {
            error!("Failed to list VReplicaSets");
            return Err(Error::VReplicaSetListFailed);
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
            info!("Processing manifest: {:?}", path);

            // apply manifest
            let vrs_name = apply_file(path.clone(), client.clone(), &discovery).await;
            match vrs_name {
                Ok(_) => {
                    if valid_manifest {
                        info!("Manifest from {} successfully created", path.display());
                    }
                    else {
                        error!("Manifest from {} created ReplicaSet when it should not have", path.display());
                        return Err(Error::VReplicaSetInvalidAdmissionPassed);
                    }
                }
                Err(e) => {
                    if valid_manifest {
                        error!("Manifest from {} failed to create ReplicaSet when it should have been successful. {}", path.display(), e);
                        return Err(Error::VReplicaSetValidAdmissionFailed);
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