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
            return Err(Error::Timeout);
        }
        // Check configmap
        let configmaps: Api<ConfigMap> = Api::default_namespaced(client.clone());
        let cm = configmaps.get(&rabbitmq_cm_name).await;
        match cm {
            Err(e) => {
                println!("Get configmap failed with {}, continue to wait.", e);
                continue;
            }
            Ok(cm) => {
                let data = cm.data.unwrap();
                let user_config = data.get("userDefinedConfiguration.conf").unwrap();
                if !user_config.contains("default_user = new_user")
                    || !user_config.contains("default_pass = new_pass")
                {
                    println!(
                        "Configmap is not consistent with rabbitmq cluster spec. E2e test failed."
                    );
                    return Err(Error::RabbitmqConfigMapFailed);
                }
                println!("Configmap is found as expected.");
            }
        };
        // Check statefulset
        let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
        let sts = sts_api.get(&rabbitmq_sts_name).await;
        match sts {
            Err(e) => {
                println!("Get statefulset failed with {}, continue to wait.", e);
                continue;
            }
            Ok(sts) => {
                if sts.spec.unwrap().replicas != Some(3) {
                    println!("Statefulset spec is not consistent with rabbitmq cluster spec. E2e test failed.");
                    return Err(Error::RabbitmqStsFailed);
                }
                println!("Statefulset is found as expected.");
            }
        };

        // Check pods
        let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
        let lp = ListParams::default().labels(&format!("app={}", &rabbitmq_name)); // only want results for our pod
        let pod_list = pod_api.list(&lp).await?;
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
                    "Pod {} is not ready. Continue to wait.",
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
    println!("Desired state test passed.");
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
        println!("User and password test failed with {}.", err);
        return Err(Error::RabbitmqUserPassFailed);
    } else {
        println!("{}", out);
    }
    println!("Authenticate user test passed.");
    Ok(())
}

pub async fn rabbitmq_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crds: Api<CustomResourceDefinition> = Api::all(client.clone());
    let rabbitmq_crd = crds.get("rabbitmqclusters.anvil.dev").await;
    match rabbitmq_crd {
        Err(e) => {
            println!("No CRD found, create one before run the e2e test.");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            println!("CRD found, continue to run the e2e test.");
        }
    }

    // create a rabbitmq cluster
    let discovery = Discovery::new(client.clone()).run().await?;
    let rabbitmq_name = apply(rabbitmq_cluster(), client.clone(), &discovery).await?;

    desired_state_test(client.clone(), rabbitmq_name.clone()).await?;
    authenticate_user_test(client.clone(), rabbitmq_name.clone()).await?;

    println!("E2e test passed.");
    Ok(())
}
