#![allow(unused_imports)]
#![allow(unused_variables)]
use futures::{StreamExt, TryStreamExt};
use k8s_openapi::api::apps::v1::StatefulSet;
use k8s_openapi::api::core::v1::{ConfigMap, Pod};
use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition;
use kube::Resource;
use kube::{
    api::{
        Api, AttachParams, AttachedProcess, DeleteParams, ListParams, Patch, PatchParams,
        PostParams, ResourceExt,
    },
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

#[derive(kube::CustomResource, Debug, Clone, Deserialize, Serialize, schemars::JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "RabbitmqCluster")]
#[kube(shortname = "rbmq", namespaced)]
pub struct RabbitmqClusterSpec {
    pub replicas: i32,
    #[serde(rename = "rabbitmq", skip_serializing_if = "Option::is_none")]
    pub rabbitmq_config: Option<RabbitmqClusterConfigurationSpec>,
}
#[derive(Debug, Clone, Deserialize, Serialize, schemars::JsonSchema)]
pub struct RabbitmqClusterConfigurationSpec {
    // #[serde(rename = "additionalPlugins", skip_serializing_if = "Option::is_none")]
    // pub additional_plugins: Option<Vec<String>>,
    #[serde(rename = "additionalConfig", skip_serializing_if = "Option::is_none")]
    pub additional_config: Option<String>,
    #[serde(rename = "advancedConfig", skip_serializing_if = "Option::is_none")]
    pub advanced_config: Option<String>,
    #[serde(rename = "envConfig", skip_serializing_if = "Option::is_none")]
    pub env_config: Option<String>,
}

pub async fn rabbitmq_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crds: Api<CustomResourceDefinition> = Api::all(client.clone());
    let rabbitmq_crd = crds.get("rabbitmqclusters.anvil.dev").await;
    match rabbitmq_crd {
        Err(e) => {
            println!("No CRD found, create one before run the e2e test!\n");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            println!("CRD found, continue to run the e2e test!\n");
        }
    }

    // create a rabbitmq cluster
    let pp = PostParams::default();
    let rabbitmq_api: Api<RabbitmqCluster> = Api::namespaced(client.clone(), "default");
    let rabbitmq_name = "rabbitmq-test";
    let rabbitmq_sts_name = format!("{}-server", &rabbitmq_name);
    let rabbitmq_cm_name = format!("{}-server-conf", &rabbitmq_name);
    let rabbitmq = RabbitmqCluster::new(
        &rabbitmq_name,
        RabbitmqClusterSpec {
            replicas: 3,
            rabbitmq_config: Some(RabbitmqClusterConfigurationSpec {
                additional_config: Some(String::from(
                    "default_user=new_user\ndefault_pass=new_pass",
                )),
                advanced_config: None,
                env_config: None,
            }),
        },
    );
    let o = rabbitmq_api.create(&pp, &rabbitmq).await?;
    assert_eq!(ResourceExt::name_any(&rabbitmq), ResourceExt::name_any(&o));
    println!("Created {}", o.name_any());

    let seconds = Duration::from_secs(360);
    let start = Instant::now();
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > seconds {
            return Err(Error::Timeout);
        }
        // Check configmap
        let configmaps: Api<ConfigMap> = Api::default_namespaced(client.clone());
        let cm = configmaps.get(&rabbitmq_cm_name).await;
        match cm {
            Err(e) => {
                println!("No configmap found, continue to wait!\n");
                continue;
            }
            Ok(cm) => {
                let data = cm.data.unwrap();
                let user_config = data.get("userDefinedConfiguration.conf").unwrap();
                if !user_config.contains("default_user=new_user")
                    || !user_config.contains("default_pass=new_pass")
                {
                    println!("Configmap is not consistent with rabbitmq cluster spec! e2e_test failed!\n");
                    return Err(Error::RabbitmqConfigMapFailed);
                }
            }
        };
        // Check statefulset
        let sts_api: Api<StatefulSet> = Api::default_namespaced(client.clone());
        let sts = sts_api.get(&rabbitmq_sts_name).await;
        match sts {
            Err(e) => {
                println!("No statefulset found, continue to wait!\n");
                continue;
            }
            Ok(sts) => {
                if sts.spec.unwrap().replicas != Some(3) {
                    println!("Statefulset spec is not consistent with rabbitmq cluster spec! e2e_test failed!\n");
                    return Err(Error::RabbitmqStsFailed);
                }
                if sts.status.unwrap().replicas != 3 {
                    continue;
                }
            }
        };

        // Check pods
        let pods: Api<Pod> = Api::default_namespaced(client.clone());
        let lp = ListParams::default().labels(&format!("app={}", &rabbitmq_name)); // only want results for our pod
        let pod_list = pods.list(&lp).await?;
        if pod_list.items.len() != 3 {
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
            let attached = pods
                .exec(
                    p.metadata.name.unwrap().as_str(),
                    vec!["rabbitmqctl", "authenticate_user", "new_user", "new_pass"],
                    &AttachParams::default().stderr(true),
                )
                .await?;
            let err = get_err(attached).await;
            if err != "" {
                println!("User and password test failed!\n");
                return Err(Error::RabbitmqUserPassFailed);
            }
        }
        if pods_ready {
            break;
        }
    }
    println!("Rabbitmq cluster is ready! e2e test passed\n");
    Ok(())
}

async fn get_err(mut attached: AttachedProcess) -> String {
    let mut stderr = tokio_util::io::ReaderStream::new(attached.stderr().unwrap());
    let mut stream_contents = Vec::new();
    while let Some(chunk) = stderr.next().await {
        stream_contents.extend_from_slice(&chunk.unwrap());
    }
    attached.join().await.unwrap();
    String::from_utf8_lossy(&stream_contents).to_string()
}
