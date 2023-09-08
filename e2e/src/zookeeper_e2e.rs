#![allow(unused_imports)]
#![allow(unused_variables)]
use k8s_openapi::api::apps::v1::StatefulSet;
use k8s_openapi::api::core::v1::Pod;
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

use crate::common::*;

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
      clientPort: 2181
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

pub async fn desired_state_test(client: Client, zk_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }
        // Check stateful set
        let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
        let sts = sts_api.get(&zk_name).await;
        match sts {
            Err(e) => {
                println!("Get stateful set failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if sts.spec.unwrap().replicas != Some(3) {
                    println!("Stateful set spec is not consistent with zookeeper cluster spec. E2e test failed.");
                    return Err(Error::ZookeeperStsFailed);
                }
                println!("Stateful set is found as expected.");
                if sts.status.as_ref().unwrap().ready_replicas.is_none() {
                    println!("No stateful set pod is ready.");
                } else if *sts
                    .status
                    .as_ref()
                    .unwrap()
                    .ready_replicas
                    .as_ref()
                    .unwrap()
                    == 3
                {
                    println!("All stateful set pods are ready.");
                    break;
                } else {
                    println!(
                        "Only {} pods are ready now.",
                        sts.status
                            .as_ref()
                            .unwrap()
                            .ready_replicas
                            .as_ref()
                            .unwrap()
                    );
                }
            }
        };
    }
    println!("Desired state test passed.");
    Ok(())
}

pub async fn zk_workload_test(client: Client, zk_name: String) -> Result<(), Error> {
    let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
    let pod_name = zk_name.clone() + "-0";

    let mut attached = pod_api
        .exec(
            pod_name.as_str(),
            vec!["zkCli.sh", "create", "/test-key", "test-data"],
            &AttachParams::default().stderr(true),
        )
        .await?;
    let (out, err) = get_output_and_err(attached).await;

    attached = pod_api
        .exec(
            pod_name.as_str(),
            vec!["zkCli.sh", "get", "/test-key"],
            &AttachParams::default().stderr(true),
        )
        .await?;
    let (out, err) = get_output_and_err(attached).await;
    if err != "" {
        println!("ZK workload test failed with {}.", err);
        return Err(Error::ZookeeperWorkloadFailed);
    } else {
        println!("{}", out);
        if !out.contains("test-data") {
            println!("Test failed because of unexpected get output.");
            return Err(Error::ZookeeperWorkloadFailed);
        }
    }

    attached = pod_api
        .exec(
            pod_name.as_str(),
            vec!["zkCli.sh", "set", "/test-key", "test-data-2"],
            &AttachParams::default().stderr(true),
        )
        .await?;
    let (out, err) = get_output_and_err(attached).await;

    attached = pod_api
        .exec(
            pod_name.as_str(),
            vec!["zkCli.sh", "get", "/test-key"],
            &AttachParams::default().stderr(true),
        )
        .await?;
    let (out, err) = get_output_and_err(attached).await;
    if err != "" {
        println!("ZK workload test failed with {}.", err);
        return Err(Error::ZookeeperWorkloadFailed);
    } else {
        println!("{}", out);
        if !out.contains("test-data-2") {
            println!("Test failed because of unexpected get output.");
            return Err(Error::ZookeeperWorkloadFailed);
        }
    }

    println!("Zookeeper workload test passed.");
    Ok(())
}

pub async fn zookeeper_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crd_api: Api<CustomResourceDefinition> = Api::all(client.clone());
    let zk_crd = crd_api.get("zookeeperclusters.anvil.dev").await;
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

    desired_state_test(client.clone(), zk_name.clone()).await?;
    zk_workload_test(client.clone(), zk_name.clone()).await?;

    println!("E2e test passed.");
    Ok(())
}
