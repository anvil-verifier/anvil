#![allow(unused_imports)]
#![allow(unused_variables)]
use futures::{StreamExt, TryStreamExt};
use k8s_openapi::api::apps::v1::StatefulSet;
use k8s_openapi::api::core::v1::{ConfigMap, Pod};
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

pub fn rabbitmq_cluster() -> String {
    "
    apiVersion: anvil.dev/v1
    kind: RabbitmqCluster
    metadata:
      name: rabbitmq
      namespace: default
    spec:
      replicas: 3
      image: rabbitmq:3.11.10-management
      rabbitmqConfig:
        additionalConfig: |
          default_user = new_user
          default_pass = new_pass
    "
    .to_string()
}

pub fn rabbitmq_cluster_ephemeral() -> String {
    "
    apiVersion: anvil.dev/v1
    kind: RabbitmqCluster
    metadata:
      name: rabbitmq
      namespace: default
    spec:
      replicas: 3
      image: rabbitmq:3.11.10-management
      persistence:
        storage: 0Gi
      rabbitmqConfig:
        additionalConfig: |
          default_user = new_user
          default_pass = new_pass
    "
    .to_string()
}

pub async fn desired_state_test(client: Client, rabbitmq_name: String) -> Result<(), Error> {
    let rabbitmq_sts_name = format!("{}-server", &rabbitmq_name);
    let rabbitmq_cm_name = format!("{}-server-conf", &rabbitmq_name);
    let timeout = Duration::from_secs(600);
    let start = Instant::now();
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            error!("Time out on desired state test");
            return Err(Error::Timeout);
        }
        // Check config map
        let cm_api: Api<ConfigMap> = Api::default_namespaced(client.clone());
        let cm = cm_api.get(&rabbitmq_cm_name).await;
        match cm {
            Err(e) => {
                info!("Get config map failed with {}, continue to wait.", e);
                continue;
            }
            Ok(cm) => {
                let data = cm.data.unwrap();
                let user_config = data.get("userDefinedConfiguration.conf").unwrap();
                if !user_config.contains("default_user = new_user")
                    || !user_config.contains("default_pass = new_pass")
                {
                    error!(
                        "Config map is not consistent with rabbitmq cluster spec. E2e test failed."
                    );
                    return Err(Error::RabbitmqConfigMapFailed);
                }
                info!("Config map is found as expected.");
            }
        };
        // Check stateful set
        let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
        let sts = sts_api.get(&rabbitmq_sts_name).await;
        match sts {
            Err(e) => {
                info!("Get stateful set failed with {}, continue to wait.", e);
                continue;
            }
            Ok(sts) => {
                if sts.spec.as_ref().unwrap().replicas != Some(3) {
                    error!("Stateful set spec is not consistent with rabbitmq cluster spec. E2e test failed.");
                    return Err(Error::RabbitmqStsFailed);
                }
                info!("Stateful set is found as expected.");
                if sts.status.as_ref().unwrap().ready_replicas.is_none() {
                    info!("No stateful set pod is ready.");
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
                    info!("All stateful set pods are ready.");
                    break;
                } else {
                    info!(
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
    info!("Desired state test passed.");
    Ok(())
}

pub async fn relabel_test(client: Client, rabbitmq_name: String) -> Result<(), Error> {
    let rabbitmq_sts_name = format!("{}-server", &rabbitmq_name);
    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
    run_command(
        "kubectl",
        vec![
            "patch",
            "rbmq",
            "rabbitmq",
            "--type=json",
            "-p",
            "[{\"op\": \"add\", \"path\": \"/spec/labels/key\", \"value\": \"val\"}]",
        ],
        "failed to relabel rabbitmq",
    );

    // Sleep for extra 5 seconds to ensure the upgrading has started
    sleep(Duration::from_secs(5)).await;
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            error!("Time out on relabel test");
            return Err(Error::Timeout);
        }

        // Check stateful set
        let sts = sts_api.get(&rabbitmq_sts_name).await;
        match sts {
            Err(e) => {
                info!("Get stateful set failed with error {}.", e);
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
                    info!("Label for pod is not updated yet");
                    continue;
                }

                if sts.status.as_ref().unwrap().updated_replicas.is_none() {
                    info!("No stateful set pod is updated yet.");
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
                    info!("Relabel is done.");
                } else {
                    info!(
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
                    info!("No stateful set pod is ready.");
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
                    info!("All stateful set pods are ready.");
                    break;
                } else {
                    info!(
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

    info!("Relabel test passed.");
    Ok(())
}

pub async fn reconfiguration_test(client: Client, rabbitmq_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
    let rabbitmq_sts_name = format!("{}-server", &rabbitmq_name);
    run_command(
        "kubectl",
        vec![
            "patch",
            "rbmq",
            "rabbitmq",
            "--type=json",
            "-p",
            "[{\"op\": \"replace\", \"path\": \"/spec/rabbitmqConfig/additionalConfig\", \"value\": \"log.console = true\\nlog.console.level = debug\\nlog.console.formatter = json\\n\"}]",
        ],
        "failed to reconfigure rabbitmq",
    );

    // Sleep for extra 5 seconds to ensure the reconfiguration has started
    sleep(Duration::from_secs(5)).await;
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            error!("Time out on reconfiguration test");
            return Err(Error::Timeout);
        }

        // Check stateful set
        let sts = sts_api.get(&rabbitmq_sts_name).await;
        match sts {
            Err(e) => {
                info!("Get stateful set failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if sts.status.as_ref().unwrap().updated_replicas.is_none() {
                    info!("No stateful set pod is updated yet.");
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
                    info!("Reconfiguration is done.");
                } else {
                    info!(
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
                    info!("No stateful set pod is ready.");
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
                    info!("All stateful set pods are ready.");
                    break;
                } else {
                    info!(
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

    // Check if the configuration file used by the rabbitmq server is actually updated
    let pod_name = rabbitmq_name + "-server-0";
    let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
    let attached = pod_api
        .exec(
            pod_name.as_str(),
            vec![
                "cat",
                "/etc/rabbitmq/conf.d/90-userDefinedConfiguration.conf",
            ],
            &AttachParams::default().stderr(true),
        )
        .await?;
    let (out, err) = get_output_and_err(attached).await;
    if err != "" {
        error!("Reconfiguration test failed with {}.", err);
        return Err(Error::ZookeeperWorkloadFailed);
    } else {
        info!("The config file is: {}", out);
        if !out.contains("log.console = true")
            || !out.contains("log.console.level = debug")
            || !out.contains("log.console.formatter = json")
        {
            error!("Test failed because of unexpected zoo.cfg data.");
            return Err(Error::ZookeeperWorkloadFailed);
        }
    }

    info!("Reconfiguration test passed.");
    Ok(())
}

pub async fn scaling_test(client: Client, rabbitmq_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
    let rabbitmq_sts_name = format!("{}-server", &rabbitmq_name);

    run_command(
        "kubectl",
        vec![
            "patch",
            "rbmq",
            "rabbitmq",
            "--type=json",
            "-p",
            "[{\"op\": \"replace\", \"path\": \"/spec/replicas\", \"value\": 4}]",
        ],
        "failed to scale rabbitmq",
    );

    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            error!("Time out on scaling test");
            return Err(Error::Timeout);
        }

        let sts = sts_api.get(&rabbitmq_sts_name).await;
        match sts {
            Err(e) => {
                info!("Get stateful set failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if sts.spec.unwrap().replicas != Some(4) {
                    info!("Stateful set spec is not consistent with rabbitmq cluster spec yet.");
                    continue;
                }
                info!("Stateful set is found as expected.");
                if sts.status.as_ref().unwrap().ready_replicas.is_none() {
                    info!("No stateful set pod is ready.");
                    continue;
                } else if *sts
                    .status
                    .as_ref()
                    .unwrap()
                    .ready_replicas
                    .as_ref()
                    .unwrap()
                    == 4
                {
                    info!("Scale up is done with 4 replicas ready.");
                    break;
                } else {
                    info!(
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
    info!("Scaling test passed.");
    Ok(())
}

pub async fn upgrading_test(client: Client, rabbitmq_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
    let rabbitmq_sts_name = format!("{}-server", &rabbitmq_name);
    run_command(
        "kubectl",
        vec![
            "patch",
            "rbmq",
            "rabbitmq",
            "--type=json",
            "-p",
            "[{\"op\": \"replace\", \"path\": \"/spec/image\", \"value\": \"rabbitmq:3.11.20-management\"}]",
        ],
        "failed to upgrade rabbitmq",
    );

    // Sleep for extra 5 seconds to ensure the upgrading has started
    sleep(Duration::from_secs(5)).await;
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            error!("Time out on upgrading test");
            return Err(Error::Timeout);
        }

        // Check stateful set
        let sts = sts_api.get(&rabbitmq_sts_name).await;
        match sts {
            Err(e) => {
                info!("Get stateful set failed with error {}.", e);
                continue;
            }
            Ok(sts) => {
                if sts.status.as_ref().unwrap().updated_replicas.is_none() {
                    info!("No stateful set pod is updated yet.");
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
                    info!("Upgrading is done.");
                } else {
                    info!(
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
                    info!("No stateful set pod is ready.");
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
                    info!("All stateful set pods are ready.");
                    break;
                } else {
                    info!(
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

    info!("Upgrading test passed.");
    Ok(())
}

pub async fn authenticate_user_test(client: Client, rabbitmq_name: String) -> Result<(), Error> {
    let pod_name = rabbitmq_name + "-server-0";
    let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
    let attached = pod_api
        .exec(
            pod_name.as_str(),
            vec!["rabbitmqctl", "authenticate_user", "new_user", "new_pass"],
            &AttachParams::default().stderr(true),
        )
        .await?;
    let (out, err) = get_output_and_err(attached).await;
    if err != "" {
        error!("User and password test failed with {}.", err);
        return Err(Error::RabbitmqUserPassFailed);
    } else {
        info!("{}", out);
    }
    info!("Authenticate user test passed.");
    Ok(())
}

pub async fn rabbitmq_workload_test(client: Client, rabbitmq_name: String) -> Result<(), Error> {
    run_command(
        "kubectl",
        vec![
            "run",
            "perf-test",
            "--image=pivotalrabbitmq/perf-test",
            "--",
            "--uri",
            "\"amqp://new_user:new_pass@rabbitmq-client\"",
        ],
        "failed to run perf test pod",
    );
    let pod_name = "perf-test";
    let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
    let timeout = Duration::from_secs(600);
    let perf_test_duration = Duration::from_secs(20);
    let start = Instant::now();
    let mut perf_test_start: Option<Instant> = None;
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            error!("Time out on perf test");
            return Err(Error::Timeout);
        }
        match pod_api.get(pod_name).await {
            Err(e) => {
                info!("Get pod failed with {}, continue to wait.", e);
                continue;
            }
            Ok(pod) => {
                if pod.status.is_none() {
                    info!("Pod status is not available yet.");
                    continue;
                } else if pod.status.unwrap().phase != Some("Running".to_string()) {
                    info!("Perf test pod is not running yet.");
                    continue;
                } else {
                    if perf_test_start.is_none() {
                        info!("Perf test starts running.");
                        perf_test_start = Some(Instant::now());
                        continue;
                    } else {
                        if perf_test_start.unwrap().elapsed() > perf_test_duration {
                            break;
                        } else {
                            info!("Keep running perf test.");
                            continue;
                        }
                    }
                }
            }
        };
    }
    // Shall we delete the perf test pod here?
    info!("Rabbitmq workload test passed.");
    Ok(())
}

pub async fn rabbitmq_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crd_api: Api<CustomResourceDefinition> = Api::all(client.clone());
    let rabbitmq_crd = crd_api.get("rabbitmqclusters.anvil.dev").await;
    match rabbitmq_crd {
        Err(e) => {
            error!("No CRD found, create one before run the e2e test.");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            info!("CRD found, continue to run the e2e test.");
        }
    }

    // create a rabbitmq cluster
    let discovery = Discovery::new(client.clone()).run().await?;
    let rabbitmq_name = apply(rabbitmq_cluster(), client.clone(), &discovery).await?;

    desired_state_test(client.clone(), rabbitmq_name.clone()).await?;
    relabel_test(client.clone(), rabbitmq_name.clone()).await?;
    reconfiguration_test(client.clone(), rabbitmq_name.clone()).await?;
    authenticate_user_test(client.clone(), rabbitmq_name.clone()).await?;
    upgrading_test(client.clone(), rabbitmq_name.clone()).await?;
    rabbitmq_workload_test(client.clone(), rabbitmq_name.clone()).await?;

    info!("E2e test passed.");
    Ok(())
}

pub async fn rabbitmq_scaling_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crd_api: Api<CustomResourceDefinition> = Api::all(client.clone());
    let rabbitmq_crd = crd_api.get("rabbitmqclusters.anvil.dev").await;
    match rabbitmq_crd {
        Err(e) => {
            error!("No CRD found, create one before run the e2e test.");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            info!("CRD found, continue to run the e2e test.");
        }
    }

    // create a rabbitmq cluster
    let discovery = Discovery::new(client.clone()).run().await?;
    let rabbitmq_name = apply(rabbitmq_cluster(), client.clone(), &discovery).await?;

    desired_state_test(client.clone(), rabbitmq_name.clone()).await?;
    scaling_test(client.clone(), rabbitmq_name.clone()).await?;
    rabbitmq_workload_test(client.clone(), rabbitmq_name.clone()).await?;

    info!("E2e test passed.");
    Ok(())
}

pub async fn rabbitmq_ephemeral_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crd_api: Api<CustomResourceDefinition> = Api::all(client.clone());
    let rabbitmq_crd = crd_api.get("rabbitmqclusters.anvil.dev").await;
    match rabbitmq_crd {
        Err(e) => {
            error!("No CRD found, create one before run the e2e test.");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            info!("CRD found, continue to run the e2e test.");
        }
    }

    // create a rabbitmq cluster
    let discovery = Discovery::new(client.clone()).run().await?;
    let rabbitmq_name = apply(rabbitmq_cluster_ephemeral(), client.clone(), &discovery).await?;

    desired_state_test(client.clone(), rabbitmq_name.clone()).await?;
    scaling_test(client.clone(), rabbitmq_name.clone()).await?;
    rabbitmq_workload_test(client.clone(), rabbitmq_name.clone()).await?;

    info!("E2e test passed.");
    Ok(())
}
