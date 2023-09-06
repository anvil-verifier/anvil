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

pub fn zookeeper_cluster() -> String {
    "
    apiVersion: anvil.dev/v1
    kind: ZookeeperCluster
    metadata:
      name: zookeeper
      namespace: default
    spec:
      replicas: 3
      image: pravega/zookeeper:0.2.14
      resources:
        requests:
          memory: \"256Mi\"
          cpu: \"500m\"
      conf:
        initLimit: 10
        syncLimit: 2
        tickTime: 2000
        globalOutstandingLimit: 1000
        preAllocSize: 65536
        snapCount: 10000
        commitLogCount: 500
        snapSizeLimitInKb: 4194304
        maxCnxns: 0
        maxClientCnxns: 60
        minSessionTimeout: 4000
        maxSessionTimeout: 40000
        autoPurgeSnapRetainCount: 3
        autoPurgePurgeInterval: 1
        quorumListenOnAllIps: false
    "
    .to_string()
}

pub async fn zookeeper_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crds: Api<CustomResourceDefinition> = Api::all(client.clone());
    let zk_crd = crds.get("zookeeperclusters.anvil.dev").await;
    match zk_crd {
        Err(e) => {
            println!("No CRD found, create one before run the e2e test.");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            println!("CRD found, continue to run the e2e test.");
        }
    }

    // create a zookeeper cluster
    let discovery = Discovery::new(client.clone()).run().await?;
    let zk_name = apply(zookeeper_cluster(), client.clone(), &discovery).await?;

    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }
        // Check statefulset
        let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
        let sts = sts_api.get(&zk_name).await;
        match sts {
            Err(e) => {
                println!("Get statefulset failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if sts.spec.unwrap().replicas != Some(3) {
                    println!("Statefulset spec is not consistent with zookeeper cluster spec. E2e test failed.");
                    return Err(Error::ZookeeperStsFailed);
                }
                println!("Statefulset is found as expected.");
            }
        };
        // Check pods
        let pods: Api<Pod> = Api::default_namespaced(client.clone());
        let lp = ListParams::default().labels(&format!("app={}", &zk_name)); // only want results for our pod
        let pod_list = pods.list(&lp).await?;
        if pod_list.items.len() != 3 {
            println!("Pods are not ready. Continue to wait.");
            continue;
        }
        let mut pods_ready = true;
        for p in pod_list {
            let status = p.status.unwrap();
            if status.phase != Some("Running".to_string())
            // container should also be ready
            || !status.container_statuses.unwrap()[0].ready
            {
                println!(
                    "Pod {} not ready. Continue to wait.",
                    p.metadata.name.unwrap()
                );
                pods_ready = false;
                break;
            }
        }
        if pods_ready {
            break;
        }
    }
    println!("E2e test passed.");
    Ok(())
}
