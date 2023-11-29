#![allow(unused_imports)]
#![allow(unused_variables)]
use k8s_openapi::api::core::v1::{Pod, ServiceAccount, Service};
use k8s_openapi::api::rbac::v1::RoleBinding;
use k8s_openapi::api::{apps::v1::DaemonSet, rbac::v1::Role};
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

pub fn fluent_bit() -> String {
    "
    apiVersion: anvil.dev/v1
    kind: FluentBit
    metadata:
        name: fluent-bit
        namespace: default
    spec:
        fluentBitConfigName: fluent-bit-config
        image: kubesphere/fluent-bit:v2.1.7
        tolerations:
            - operator: Exists
        ports:
            - name: forward
              containerPort: 24224
              protocol: TCP
            - containerPort: 8443
              name: https
    "
    .to_string()
}

pub fn fluent_bit_config() -> String {
    "
    apiVersion: anvil.dev/v1
    kind: FluentBitConfig
    metadata:
        name: fluent-bit-config
        namespace: default
    spec:
        fluentBitConfig: |
            [Service]
                Parsers_File    parsers.conf
            [Input]
                Name    tail
                Path    /var/log/containers/*.log
                Exclude_Path    /var/log/containers/utils_default_utils-*.log
                Refresh_Interval    10
                Skip_Long_Lines    true
                DB    /fluent-bit/tail/pos.db
                DB.Sync    Normal
                Mem_Buf_Limit    5MB
                Parser    docker
                Tag    kube.*
            [Filter]
                Name    kubernetes
                Match    kube.*
                Kube_URL    https://kubernetes.default.svc:443
                Kube_CA_File    /var/run/secrets/kubernetes.io/serviceaccount/ca.crt
                Kube_Token_File    /var/run/secrets/kubernetes.io/serviceaccount/token
                Labels    false
                Annotations    false
            [Filter]
                Name    nest
                Match    kube.*
                Operation    lift
                Nested_under    kubernetes
                Add_prefix    kubernetes_
            [Filter]
                Name    modify
                Match    kube.*
                Remove    stream
                Remove    kubernetes_pod_id
                Remove    kubernetes_host
                Remove    kubernetes_container_hash
            [Filter]
                Name    nest
                Match    kube.*
                Operation    nest
                Wildcard    kubernetes_*
                Nest_under    kubernetes
                Remove_prefix    kubernetes_
            [Output]
                Name    kafka
                Match_Regex    (?:kube|service)\\.(.*)
                Brokers    my-cluster-kafka-brokers.kafka.svc:9092
                Topics    fluent-log
        parsersConfig: \"\"    
    "
    .to_string()
}

fn node_number() -> i32 {
    4
}

pub async fn desired_state_test(client: Client, fb_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }
        // Check daemon set
        let role_api: Api<Role> = Api::default_namespaced(client.clone());
        let rb_api: Api<RoleBinding> = Api::default_namespaced(client.clone());
        let svc_api: Api<Service> = Api::default_namespaced(client.clone());
        let sa_api: Api<ServiceAccount> = Api::default_namespaced(client.clone());
        let ds_api: Api<DaemonSet> = Api::default_namespaced(client.clone());

        let role = role_api.get(&(fb_name.clone() + "-role")).await;
        match role {
            Err(e) => {
                println!("Get role failed with error {}.", e);
                continue;
            }
            _ => {}
        };

        let sa = sa_api.get(&fb_name.clone()).await;
        match sa {
            Err(e) => {
                println!("Get service account failed with error {}.", e);
                continue;
            }
            _ => {}
        };

        let rb = rb_api.get(&(fb_name.clone() + "-role-binding")).await;
        match rb {
            Err(e) => {
                println!("Get role binding failed with error {}.", e);
                continue;
            }
            _ => {}
        };

        let svc = svc_api.get(&fb_name).await;
        match svc {
            Err(e) => {
                println!("Get service failed with error {}.", e);
                continue;
            }
            _ => {}
        }

        let ds = ds_api.get(&fb_name).await;
        match ds {
            Err(e) => {
                println!("Get daemon set failed with error {}.", e);
                continue;
            }
            Ok(ds) => {
                if ds.status.as_ref().unwrap().number_ready == node_number() {
                    // this number depends on the number of nodes
                    println!("All daemons are ready now.");
                    break;
                } else {
                    println!(
                        "Only {} daemons are ready now.",
                        ds.status.as_ref().unwrap().number_ready
                    );
                }
            }
        };
    }
    println!("Desired state test passed.");
    Ok(())
}

pub async fn relabel_test(client: Client, fb_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    let ds_api: Api<DaemonSet> = Api::default_namespaced(client.clone());
    run_command(
        "kubectl",
        vec![
            "patch",
            "fb",
            "fluent-bit",
            "--type=json",
            "-p",
            "[{\"op\": \"add\", \"path\": \"/spec/labels/key\", \"value\": \"val\"}]",
        ],
        "failed to relabel fb",
    );

    // Sleep for extra 5 seconds to ensure the upgrading has started
    sleep(Duration::from_secs(5)).await;
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }

        // Check daemon set
        let ds = ds_api.get(&fb_name).await;
        match ds {
            Err(e) => {
                println!("Get daemon set failed with error {}.", e);
                continue;
            }
            Ok(ds) => {
                if !ds
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

                if ds
                    .status
                    .as_ref()
                    .unwrap()
                    .updated_number_scheduled
                    .is_none()
                {
                    println!("No daemon set pod is updated yet.");
                    continue;
                } else if *ds
                    .status
                    .as_ref()
                    .unwrap()
                    .updated_number_scheduled
                    .as_ref()
                    .unwrap()
                    == node_number()
                {
                    println!("Relabel is done.");
                } else {
                    println!(
                        "Relabel is in progress. {} pods are updated now.",
                        ds.status
                            .as_ref()
                            .unwrap()
                            .updated_number_scheduled
                            .as_ref()
                            .unwrap()
                    );
                    continue;
                }

                if ds.status.as_ref().unwrap().number_ready == node_number() {
                    println!("All daemon set pods are ready.");
                    break;
                } else {
                    println!(
                        "Only {} pods are ready now.",
                        ds.status.as_ref().unwrap().number_ready
                    );
                    continue;
                }
            }
        };
    }

    println!("Relabel test passed.");
    Ok(())
}

pub async fn service_selector_test(client: Client, fb_name: String) -> Result<(), Error> {
    let timeout = Duration::from_secs(360);
    let start = Instant::now();
    let svc_api: Api<Service> = Api::default_namespaced(client.clone());
    run_command(
        "kubectl",
        vec![
            "patch",
            "fb",
            "fluent-bit",
            "--type=json",
            "-p",
            "[{\"op\": \"add\", \"path\": \"/spec/serviceSelector\", \"value\": {\"never-match-anything\": \"val\"}}]",
        ],
        "failed to set service selector to fb",
    );

    // Sleep for extra 5 seconds to ensure the upgrading has started
    sleep(Duration::from_secs(5)).await;
    loop {
        sleep(Duration::from_secs(5)).await;
        if start.elapsed() > timeout {
            return Err(Error::Timeout);
        }

        // Check daemon set
        let svc = svc_api.get(&fb_name).await;
        match svc {
            Err(e) => {
                println!("Get service failed with error {}.", e);
                continue;
            }
            Ok(svc) => {
                if svc
                    .spec
                    .as_ref()
                    .unwrap()
                    .selector
                    .as_ref()
                    .unwrap()
                    .contains_key("never-match-anything")
                {
                    println!("Selector for service is updated yet");
                    break;
                } else {
                    println!("Selector for service is not updated yet");
                }
            }
        };
    }

    println!("Service selector test passed.");
    Ok(())
}

pub async fn fluent_e2e_test() -> Result<(), Error> {
    // check if the CRD is already registered
    let client = Client::try_default().await?;
    let crd_api: Api<CustomResourceDefinition> = Api::all(client.clone());
    let fb_crd = crd_api.get("fluentbits.anvil.dev").await;
    match fb_crd {
        Err(e) => {
            println!("No CRD found, create one before run the e2e test.");
            return Err(Error::CRDGetFailed(e));
        }
        Ok(crd) => {
            println!("CRD found, continue to run the e2e test.");
        }
    }

    // create a fluent cluster
    let discovery = Discovery::new(client.clone()).run().await?;
    apply(fluent_bit_config(), client.clone(), &discovery).await?;
    let fb_name = apply(fluent_bit(), client.clone(), &discovery).await?;

    desired_state_test(client.clone(), fb_name.clone()).await?;
    relabel_test(client.clone(), fb_name.clone()).await?;
    service_selector_test(client.clone(), fb_name.clone()).await?;

    println!("E2e test passed.");
    Ok(())
}
