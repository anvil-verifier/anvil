#![allow(unused_imports)]
#![allow(unused_variables)]
use k8s_openapi::api::apps::v1::StatefulSet;
use k8s_openapi::api::core::v1::{ConfigMap, PersistentVolumeClaim, Pod, Service};
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
      ports:
        client: 2181
        quorum: 2888
        leaderElection: 3888
        metrics: 7000
        adminServer: 8080
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
      persistence:
        enabled: true
        storageSize: 20Gi
        storageClassName: standard
    "
    .to_string()
}

pub fn zookeeper_cluster_ephemeral() -> String {
    "
    apiVersion: anvil.dev/v1
    kind: ZookeeperCluster
    metadata:
      name: zookeeper
      namespace: default
    spec:
      replicas: 3
      image: pravega/zookeeper:0.2.14
      ports:
        client: 2181
        quorum: 2888
        leaderElection: 3888
        metrics: 7000
        adminServer: 8080
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
      persistence:
        enabled: false
        storageSize: 20Gi
        storageClassName: standard
    "
    .to_string()
}

pub async fn desired_state_test(client: Client, zk_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(600);
    let start = Instant::now();
    let svc_api: Api<Service> = Api::default_namespaced(client.clone());
    let cm_api: Api<ConfigMap> = Api::default_namespaced(client.clone());
    let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }

        let svc = svc_api.get(&(zk_name.clone() + "-headless")).await;
        match svc {
            Err(e) => {
                println!("Get headless service failed with error {}.", e);
                continue;
            }
            _ => {}
        };

        let svc = svc_api.get(&(zk_name.clone() + "-client")).await;
        match svc {
            Err(e) => {
                println!("Get client service failed with error {}.", e);
                continue;
            }
            _ => {}
        };

        let svc = svc_api.get(&(zk_name.clone() + "-admin-server")).await;
        match svc {
            Err(e) => {
                println!("Get admin server service failed with error {}.", e);
                continue;
            }
            _ => {}
        };

        let cm = cm_api.get(&(zk_name.clone() + "-configmap")).await;
        match cm {
            Err(e) => {
                println!("Get config map failed with error {}.", e);
                continue;
            }
            _ => {}
        };

        // Check stateful set
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
                    continue;
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
                    continue;
                }
            }
        };
    }
    println!("Desired state test passed.");
    Ok(())
}

pub async fn status_test(client: Client, zk_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(360);
    let start = Instant::now();

    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }
        if run_command(
            "kubectl",
            vec!["get", "zk", "zookeeper", "-o", "yaml"],
            "failed to get zk",
        )
        .0
        .contains("ready_replicas: 3")
        {
            println!("Status gets updated to 3 ready replicas now.");
            break;
        }
    }
    println!("Status test passed.");
    Ok(())
}

pub async fn scaling_test(client: Client, zk_name: String, persistent: bool) -> Result<(), Error> {
    let timeout = Duration::from_secs(600);
    let mut start = Instant::now();
    let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
    let pvc_api: Api<PersistentVolumeClaim> = Api::default_namespaced(client.clone());

    run_command(
        "kubectl",
        vec![
            "patch",
            "zk",
            "zookeeper",
            "--type=json",
            "-p",
            "[{\"op\": \"replace\", \"path\": \"/spec/replicas\", \"value\": 5}]",
        ],
        "failed to scale zk",
    );

    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }

        // Check stateful set
        let sts = sts_api.get(&zk_name).await;
        match sts {
            Err(e) => {
                println!("Get stateful set failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if sts.spec.unwrap().replicas != Some(5) {
                    println!(
                        "Stateful set spec is not consistent with zookeeper cluster spec yet."
                    );
                    continue;
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
                    == 5
                {
                    println!("Scale up is done with 5 replicas ready.");
                    break;
                } else {
                    println!(
                        "Scale up is in progress. {} pods are ready now.",
                        sts.status
                            .as_ref()
                            .unwrap()
                            .ready_replicas
                            .as_ref()
                            .unwrap()
                    );
                    continue;
                }
            }
        };
    }

    start = Instant::now();
    run_command(
        "kubectl",
        vec![
            "patch",
            "zk",
            "zookeeper",
            "--type=json",
            "-p",
            "[{\"op\": \"replace\", \"path\": \"/spec/replicas\", \"value\": 3}]",
        ],
        "failed to scale zk",
    );

    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }

        // Check stateful set
        let sts = sts_api.get(&zk_name).await;
        match sts {
            Err(e) => {
                println!("Get stateful set failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if sts.spec.unwrap().replicas != Some(3) {
                    println!(
                        "Stateful set spec is not consistent with zookeeper cluster spec yet."
                    );
                    continue;
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
                    if !persistent {
                        println!("Scale down is done with 3 pods ready.");
                        break;
                    } else {
                        let pvcs = pvc_api.list(&ListParams::default()).await;
                        let pvc_num = pvcs.unwrap().items.len();
                        if pvc_num == 3 {
                            println!("Scale down is done with 3 pods ready and 3 pvcs.");
                            break;
                        } else {
                            println!("Scale down is in progress. {} pvcs exist", pvc_num);
                            continue;
                        }
                    }
                } else {
                    println!(
                        "Scale down is in progress. {} pods are ready now.",
                        sts.status
                            .as_ref()
                            .unwrap()
                            .ready_replicas
                            .as_ref()
                            .unwrap()
                    );
                    continue;
                }
            }
        };
    }

    start = Instant::now();
    run_command(
        "kubectl",
        vec![
            "patch",
            "zk",
            "zookeeper",
            "--type=json",
            "-p",
            "[{\"op\": \"replace\", \"path\": \"/spec/replicas\", \"value\": 5}]",
        ],
        "failed to scale zk",
    );

    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }

        let sts = sts_api.get(&zk_name).await;
        match sts {
            Err(e) => {
                println!("Get stateful set failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if sts.spec.unwrap().replicas != Some(5) {
                    println!(
                        "Stateful set spec is not consistent with zookeeper cluster spec yet."
                    );
                    continue;
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
                    == 5
                {
                    println!("Scale up is done with 5 replicas ready.");
                    break;
                } else {
                    println!(
                        "Scale up is in progress. {} pods are ready now.",
                        sts.status
                            .as_ref()
                            .unwrap()
                            .ready_replicas
                            .as_ref()
                            .unwrap()
                    );
                    continue;
                }
            }
        };
    }

    println!("Scaling test passed.");
    Ok(())
}

pub async fn relabel_test(client: Client, zk_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(600);
    let start = Instant::now();
    let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
    run_command(
        "kubectl",
        vec![
            "patch",
            "zk",
            "zookeeper",
            "--type=json",
            "-p",
            "[{\"op\": \"add\", \"path\": \"/spec/labels/key\", \"value\": \"val\"}]",
        ],
        "failed to relabel zk",
    );

    // Sleep for extra 5 seconds to ensure the upgrading has started
    sleep(Duration::from_secs(5)).await;
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }

        // Check stateful set
        let sts = sts_api.get(&zk_name).await;
        match sts {
            Err(e) => {
                println!("Get stateful set failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if !sts
                    .spec
                    .as_ref()
                    .unwrap()
                    .template
                    .metadata
                    .as_ref()
                    .unwrap()
                    .labels
                    .as_ref()
                    .unwrap()
                    .contains_key("key")
                {
                    println!("Label for pod is not updated yet");
                    continue;
                }

                if sts.status.as_ref().unwrap().updated_replicas.is_none() {
                    println!("No stateful set pod is updated yet.");
                    continue;
                } else if *sts
                    .status
                    .as_ref()
                    .unwrap()
                    .updated_replicas
                    .as_ref()
                    .unwrap()
                    == 3
                {
                    println!("Relabel is done.");
                } else {
                    println!(
                        "Relabel is in progress. {} pods are updated now.",
                        sts.status
                            .as_ref()
                            .unwrap()
                            .updated_replicas
                            .as_ref()
                            .unwrap()
                    );
                    continue;
                }

                if sts.status.as_ref().unwrap().ready_replicas.is_none() {
                    println!("No stateful set pod is ready.");
                    continue;
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
                    continue;
                }
            }
        };
    }

    println!("Relabel test passed.");
    Ok(())
}

pub async fn upgrading_test(client: Client, zk_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(600);
    let start = Instant::now();
    let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
    run_command(
        "kubectl",
        vec![
            "patch",
            "zk",
            "zookeeper",
            "--type=json",
            "-p",
            "[{\"op\": \"replace\", \"path\": \"/spec/image\", \"value\": \"pravega/zookeeper:0.2.15\"}]",
        ],
        "failed to upgrade zk",
    );

    // Sleep for extra 5 seconds to ensure the upgrading has started
    sleep(Duration::from_secs(5)).await;
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }

        // Check stateful set
        let sts = sts_api.get(&zk_name).await;
        match sts {
            Err(e) => {
                println!("Get stateful set failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if sts.status.as_ref().unwrap().updated_replicas.is_none() {
                    println!("No stateful set pod is updated yet.");
                    continue;
                } else if *sts
                    .status
                    .as_ref()
                    .unwrap()
                    .updated_replicas
                    .as_ref()
                    .unwrap()
                    == 3
                {
                    println!("Upgrading is done.");
                } else {
                    println!(
                        "Upgrading is in progress. {} pods are updated now.",
                        sts.status
                            .as_ref()
                            .unwrap()
                            .updated_replicas
                            .as_ref()
                            .unwrap()
                    );
                    continue;
                }

                if sts.status.as_ref().unwrap().ready_replicas.is_none() {
                    println!("No stateful set pod is ready.");
                    continue;
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
                    continue;
                }
            }
        };
    }

    println!("Upgrading test passed.");
    Ok(())
}

pub async fn reconfiguration_test(client: Client, zk_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(600);
    let start = Instant::now();
    let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
    run_command(
        "kubectl",
        vec![
            "patch",
            "zk",
            "zookeeper",
            "--type=json",
            "-p",
            "[{\"op\": \"replace\", \"path\": \"/spec/conf/initLimit\", \"value\": 15}]",
        ],
        "failed to reconfigure zk",
    );

    // Sleep for extra 5 seconds to ensure the reconfiguration has started
    sleep(Duration::from_secs(5)).await;
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }

        // Check stateful set
        let sts = sts_api.get(&zk_name).await;
        match sts {
            Err(e) => {
                println!("Get stateful set failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if sts.status.as_ref().unwrap().updated_replicas.is_none() {
                    println!("No stateful set pod is updated yet.");
                    continue;
                } else if *sts
                    .status
                    .as_ref()
                    .unwrap()
                    .updated_replicas
                    .as_ref()
                    .unwrap()
                    == 3
                {
                    println!("Reconfiguration is done.");
                } else {
                    println!(
                        "Reconfiguration is in progress. {} pods are updated now.",
                        sts.status
                            .as_ref()
                            .unwrap()
                            .updated_replicas
                            .as_ref()
                            .unwrap()
                    );
                    continue;
                }

                if sts.status.as_ref().unwrap().ready_replicas.is_none() {
                    println!("No stateful set pod is ready.");
                    continue;
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
                    continue;
                }
            }
        };
    }

    // Check if the configuration file used by the zk server is actually updated
    let pod_name_0 = zk_name.clone() + "-0";
    let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
    let attached = pod_api
        .exec(
            pod_name_0.as_str(),
            vec!["cat", "/data/conf/zoo.cfg"],
            &AttachParams::default().stderr(true),
        )
        .await?;
    let (out, err) = get_output_and_err(attached).await;
    if err != "" {
        println!("Reconfiguration test failed with {}.", err);
        return Err(Error::ZookeeperWorkloadFailed);
    } else {
        println!("{}", out);
        if !out.contains("initLimit=15") {
            println!("Test failed because of unexpected zoo.cfg data.");
            return Err(Error::ZookeeperWorkloadFailed);
        }
    }

    println!("Reconfiguration test passed.");
    Ok(())
}

pub async fn zk_workload_test(client: Client, zk_name: String) -> Result<(), Error> {
    let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
    let pod_name_0 = zk_name.clone() + "-0";
    let pod_name_1 = zk_name.clone() + "-1";

    // Sleep for extra 10 seconds to ensure the cluster is stable now
    sleep(Duration::from_secs(10)).await;

    let mut attached = pod_api
        .exec(
            pod_name_0.as_str(),
            vec!["zkCli.sh", "create", "/test-key", "test-data"],
            &AttachParams::default().stderr(true),
        )
        .await?;
    let (out, err) = get_output_and_err(attached).await;

    attached = pod_api
        .exec(
            pod_name_0.as_str(),
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
            pod_name_0.as_str(),
            vec!["zkCli.sh", "set", "/test-key", "test-data-2"],
            &AttachParams::default().stderr(true),
        )
        .await?;
    let (out, err) = get_output_and_err(attached).await;

    attached = pod_api
        .exec(
            pod_name_0.as_str(),
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

    // Try to read data from another zookeeper node
    attached = pod_api
        .exec(
            pod_name_1.as_str(),
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

pub async fn zk_workload_test2(client: Client, zk_name: String) -> Result<(), Error> {
    let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
    let pod_name_0 = zk_name.clone() + "-0";

    // Sleep for extra 10 seconds to ensure the cluster is stable now
    sleep(Duration::from_secs(10)).await;

    let attached = pod_api
        .exec(
            pod_name_0.as_str(),
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

    println!("Zookeeper workload test2 passed.");
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
    status_test(client.clone(), zk_name.clone()).await?;
    relabel_test(client.clone(), zk_name.clone()).await?;
    reconfiguration_test(client.clone(), zk_name.clone()).await?;
    zk_workload_test(client.clone(), zk_name.clone()).await?;
    upgrading_test(client.clone(), zk_name.clone()).await?;
    zk_workload_test2(client.clone(), zk_name.clone()).await?; // Test if the data is still there after upgrading

    println!("E2e test passed.");
    Ok(())
}

pub async fn zookeeper_scaling_e2e_test() -> Result<(), Error> {
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
    status_test(client.clone(), zk_name.clone()).await?;
    scaling_test(client.clone(), zk_name.clone(), true).await?;
    zk_workload_test(client.clone(), zk_name.clone()).await?;

    println!("E2e test passed.");
    Ok(())
}

pub async fn zookeeper_ephemeral_e2e_test() -> Result<(), Error> {
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
    let zk_name = apply(zookeeper_cluster_ephemeral(), client.clone(), &discovery).await?;

    desired_state_test(client.clone(), zk_name.clone()).await?;
    status_test(client.clone(), zk_name.clone()).await?;
    scaling_test(client.clone(), zk_name.clone(), false).await?;
    zk_workload_test(client.clone(), zk_name.clone()).await?;

    println!("E2e test passed.");
    Ok(())
}
