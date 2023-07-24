#![allow(unused_imports)]
#![allow(unused_variables)]
use k8s_openapi::api::apps::v1::StatefulSet;
use k8s_openapi::api::core::v1::Pod;
use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition;
use kube::{
    api::{Api, DeleteParams, ListParams, Patch, PatchParams, PostParams, ResourceExt},
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

use crate::common::apply;
use crate::common::Error;

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
    let discovery = Discovery::new(client.clone()).run().await?;
    let pth = PathBuf::from("./zookeeper.yaml");
    let zk_name = apply(pth, client.clone(), &discovery).await?;

    let init_replicas = 3;
    println!("Zookeeper cluster is ready! e2e test passed\n");
    Ok(())
}

async fn expect_zk_reach(
    zk_name: &String,
    client: &Client,
    wanted_replicas: i32,
) -> Result<(), Error> {
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
                if sts.spec.unwrap().replicas != Some(wanted_replicas) {
                    println!("Statefulset spec is not consistent with zookeeper cluster spec! e2e_test failed!\n");
                    return Err(Error::ZookeeperStsFailed);
                }
                if sts.status.unwrap().replicas != wanted_replicas {
                    continue;
                }
            }
        };
        // Check pods
        let pods: Api<Pod> = Api::default_namespaced(client.clone());
        let lp = ListParams::default().labels(&format!("app={}", &zk_name)); // only want results for our pod
        let pod_list = pods.list(&lp).await?;
        if pod_list.items.len() != wanted_replicas as usize {
            println!("Pods are not ready! Continue to wait!\n");
            continue;
        }
        let mut pods_ready = true;
        for p in pod_list {
            let status = p.status.unwrap();
            if status.phase != Some("Running".to_string())
            // container should also be ready
            || !status.container_statuses.unwrap()[0].ready
            {
                println!("Pods are not ready! Continue to wait!\n");
                pods_ready = false;
                break;
            }
        }
        if pods_ready {
            // check scale down and scale up
            break;
        }
    }
    Ok(())
}
