#![allow(unused_imports)]
#![allow(unused_variables)]
use k8s_openapi::api::apps::v1::StatefulSet;
use k8s_openapi::api::core::v1::Pod;
use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition;
use kube::{
    api::{Api, DeleteParams, ListParams, Patch, PatchParams, PostParams, ResourceExt},
    core::crd::CustomResourceExt,
    Client, CustomResource,
};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::thread;
use std::time::{Duration, Instant};
use tokio::time::sleep;

use crate::error::Error;

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "ZookeeperCluster")]
#[kube(shortname = "zk", namespaced)]
pub struct ZookeeperClusterSpec {
    pub replicas: i32,
}

pub async fn zookeeper_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crds: Api<CustomResourceDefinition> = Api::all(client.clone());
    let zk_crd = crds.get("zookeeperclusters.anvil.dev").await;
    match zk_crd {
        Err(e) => {
            println!("No CRD found, create one before run the e2e test!\n");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            println!("CRD found, continue to run the e2e test!\n");
        }
    }

    // create a zookeeper cluster

    let pp = PostParams::default();
    let zk_api: Api<ZookeeperCluster> = Api::namespaced(client.clone(), "default");
    let zk_name = "zk-test";
    let zk = ZookeeperCluster::new(&zk_name, ZookeeperClusterSpec { replicas: 3 });
    let o = zk_api.create(&pp, &zk).await?;
    assert_eq!(ResourceExt::name_any(&zk), ResourceExt::name_any(&o));
    println!("Created {}", o.name_any());

    let seconds = Duration::from_secs(360);
    let start = Instant::now();
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > seconds {
            return Err(Error::Timeout);
        }
        // Check statefulset
        let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
        let sts = sts_api.get(&zk_name).await;
        match sts {
            Err(e) => {
                println!("No statefulset found, continue to wait!\n");
                continue;
            }
            Ok(sts) => {
                if sts.spec.unwrap().replicas != Some(3) {
                    println!("Statefulset spec is not consistent with zookeeper cluster spec! e2e_test failed!\n");
                    return Err(Error::ZookeeperStsFailed);
                }
                if sts.status.unwrap().replicas != 3 {
                    continue;
                }
            }
        };
        // Check pods
        let pods: Api<Pod> = Api::default_namespaced(client.clone());
        let lp = ListParams::default().fields(&format!(
            "metadata.name={}-0,metadata.name={}-1,metadata.name={}-2",
            &zk_name, &zk_name, &zk_name
        )); // only want results for our pod
        for p in pods.list(&lp).await? {
            if p.status.unwrap().phase != Some("Running".to_string()) {
                continue;
            }
        }
        break;
    }
    println!("Zookeeper cluster is ready! e2e test passed\n");
    Ok(())
}
