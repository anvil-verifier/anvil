// Nightly clippy (0.1.64) considers Drop a side effect, see https://github.com/rust-lang/rust-clippy/issues/9608
#![allow(clippy::unnecessary_lazy_evaluations)]

pub mod fluent_types;

use anyhow::Result;
use futures::StreamExt;
use k8s_openapi::api::apps::v1::{self as appsv1, DaemonSet};
use k8s_openapi::api::core::v1::{self as corev1, Secret, ServiceAccount};
use k8s_openapi::api::rbac::v1::{self as rbacv1, ClusterRole, ClusterRoleBinding};
use k8s_openapi::apimachinery::pkg::apis::meta::v1::{self as metav1};
use k8s_openapi::ByteString;
use kube::{
    api::{Api, ListParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_client;
use kube_core::{self, ObjectMeta};
use std::collections::BTreeMap;
use std::{env, sync::Arc};
use thiserror::Error;
use tokio::time::Duration;
use tracing::*;

use crate::fluent_types::*;

#[derive(Debug, Error)]
enum Error {
    #[error("Failed to get CR: {0}")]
    CRGetFailed(#[source] kube::Error),
    #[error("Failed to reconcile Role: {0}")]
    ReconcileRoleFailed(#[source] kube::Error),
    #[error("Failed to reconcile ServiceAccount: {0}")]
    ReconcileServiceAccountFailed(#[source] kube::Error),
    #[error("Failed to reconcile RoleBinding: {0}")]
    ReconcileRoleBindingFailed(#[source] kube::Error),
    #[error("Failed to reconcile Secret: {0}")]
    ReconcileSecretFailed(#[source] kube::Error),
    #[error("Failed to reconcile DaemonSet: {0}")]
    ReconcileDaemonSetFailed(#[source] kube::Error),
    #[error("MissingObjectKey: {0}")]
    MissingObjectKey(&'static str),
}

fn make_cluster_role_name() -> String {
    "fluent-bit-role".to_string()
}

fn make_cluster_role() -> ClusterRole {
    ClusterRole {
        metadata: ObjectMeta {
            name: Some(make_cluster_role_name()),
            ..ObjectMeta::default()
        },
        rules: Some(vec![rbacv1::PolicyRule {
            api_groups: Some(vec!["".to_string()]),
            resources: Some(vec!["pods".to_string()]),
            verbs: vec!["get".to_string()],
            ..Default::default()
        }]),
        ..ClusterRole::default()
    }
}

async fn reconcile_cluster_role(_fb: &FluentBit, client: Client) -> Result<(), Error> {
    let cluster_role_api = Api::<ClusterRole>::all(client.clone());
    let cluster_role = make_cluster_role();
    info!(
        "Create cluster role: {}",
        cluster_role.metadata.name.as_ref().unwrap()
    );
    match cluster_role_api
        .create(&PostParams::default(), &cluster_role)
        .await
    {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" =>
            {
                return Ok(())
            }
            _ => return Err(Error::ReconcileRoleFailed(e)),
        },
        _ => return Ok(()),
    }
}

fn make_service_account_name(fb: &FluentBit) -> String {
    fb.metadata.name.as_ref().unwrap().clone()
}

fn make_service_account(fb: &FluentBit) -> ServiceAccount {
    ServiceAccount {
        metadata: ObjectMeta {
            name: Some(make_service_account_name(fb)),
            namespace: fb.metadata.namespace.clone(),
            ..ObjectMeta::default()
        },
        ..ServiceAccount::default()
    }
}

async fn reconcile_service_account(fb: &FluentBit, client: Client) -> Result<(), Error> {
    let service_account_api =
        Api::<ServiceAccount>::namespaced(client.clone(), fb.metadata.namespace.as_ref().unwrap());
    let service_account = make_service_account(&fb);
    info!(
        "Create service account: {}",
        service_account.metadata.name.as_ref().unwrap()
    );
    match service_account_api
        .create(&PostParams::default(), &service_account)
        .await
    {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" =>
            {
                return Ok(())
            }
            _ => return Err(Error::ReconcileServiceAccountFailed(e)),
        },
        _ => return Ok(()),
    }
}

fn make_cluster_role_binding_name(fb: &FluentBit) -> String {
    fb.metadata.name.as_ref().unwrap().clone() + "-role-binding"
}

fn make_cluster_role_binding(fb: &FluentBit) -> ClusterRoleBinding {
    ClusterRoleBinding {
        metadata: ObjectMeta {
            name: Some(make_cluster_role_binding_name(fb)),
            ..ObjectMeta::default()
        },
        role_ref: rbacv1::RoleRef {
            api_group: "rbac.authorization.k8s.io".to_string(),
            kind: "ClusterRole".to_string(),
            name: make_cluster_role_name(),
        },
        subjects: Some(vec![rbacv1::Subject {
            kind: "ServiceAccount".to_string(),
            name: make_service_account_name(fb),
            namespace: Some(fb.metadata.namespace.as_ref().unwrap().clone()),
            ..rbacv1::Subject::default()
        }]),
        ..ClusterRoleBinding::default()
    }
}

async fn reconcile_cluster_role_binding(fb: &FluentBit, client: Client) -> Result<(), Error> {
    let cluster_role_binding_api = Api::<ClusterRoleBinding>::all(client.clone());
    let cluster_role_binding = make_cluster_role_binding(&fb);
    info!(
        "Create cluster role binding: {}",
        cluster_role_binding.metadata.name.as_ref().unwrap()
    );
    match cluster_role_binding_api
        .create(&PostParams::default(), &cluster_role_binding)
        .await
    {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" =>
            {
                return Ok(())
            }
            _ => return Err(Error::ReconcileRoleBindingFailed(e)),
        },
        _ => return Ok(()),
    }
}

fn make_secret_name(fb: &FluentBit) -> String {
    fb.metadata.name.as_ref().unwrap().clone() + "-config-secret"
}

// TODO(xudong): make the configuration actually configurable
fn make_secret(fb: &FluentBit) -> Secret {
    Secret {
        metadata: ObjectMeta {
            name: Some(make_secret_name(fb)),
            namespace: fb.metadata.namespace.clone(),
            ..ObjectMeta::default()
        },
        data: Some(BTreeMap::from([
            (
                "fluent-bit.conf".to_string(),
                ByteString(
                    concat!(
                        "[Service]\n",
                        "    Parsers_File    parsers.conf\n",
                        "[Input]\n",
                        "    Name    tail\n",
                        "    Path    /var/log/containers/*.log\n",
                        "    Exclude_Path    /var/log/containers/utils_default_utils-*.log\n",
                        "    Refresh_Interval    10\n",
                        "    Skip_Long_Lines    true\n",
                        "    DB    /fluent-bit/tail/pos.db\n",
                        "    DB.Sync    Normal\n",
                        "    Mem_Buf_Limit    5MB\n",
                        "    Parser    docker\n",
                        "    Tag    kube.*\n",
                        "[Filter]\n",
                        "    Name    kubernetes\n",
                        "    Match    kube.*\n",
                        "    Kube_URL    https://kubernetes.default.svc:443\n",
                        "    Kube_CA_File    /var/run/secrets/kubernetes.io/serviceaccount/ca.crt\n",
                        "    Kube_Token_File    /var/run/secrets/kubernetes.io/serviceaccount/token\n",
                        "    Labels    false\n",
                        "    Annotations    false\n",
                        "[Filter]\n",
                        "    Name    nest\n",
                        "    Match    kube.*\n",
                        "    Operation    lift\n",
                        "    Nested_under    kubernetes\n",
                        "    Add_prefix    kubernetes_\n",
                        "[Filter]\n",
                        "    Name    modify\n",
                        "    Match    kube.*\n",
                        "    Remove    stream\n",
                        "    Remove    kubernetes_pod_id\n",
                        "    Remove    kubernetes_host\n",
                        "    Remove    kubernetes_container_hash\n",
                        "[Filter]\n",
                        "    Name    nest\n",
                        "    Match    kube.*\n",
                        "    Operation    nest\n",
                        "    Wildcard    kubernetes_*\n",
                        "    Nest_under    kubernetes\n",
                        "    Remove_prefix    kubernetes_\n",
                        "[Output]\n",
                        "    Name    kafka\n",
                        "    Match_Regex    (?:kube|service)\\.(.*)\n",
                        "    Brokers    my-cluster-kafka-brokers.kafka.svc:9092\n",
                        "    Topics    fluent-log\n"
                    )
                    .to_string()
                    .into_bytes(),
                ),
            ),
            (
                "parsers.conf".to_string(),
                ByteString("".to_string().into_bytes()),
            ),
        ])),
        ..Secret::default()
    }
}

async fn reconcile_secret(fb: &FluentBit, client: Client) -> Result<(), Error> {
    let secret_api =
        Api::<Secret>::namespaced(client.clone(), fb.metadata.namespace.as_ref().unwrap());
    let secret = make_secret(&fb);
    info!("Create secret: {}", secret.metadata.name.as_ref().unwrap());
    match secret_api.create(&PostParams::default(), &secret).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" =>
            {
                return Ok(())
            }
            _ => return Err(Error::ReconcileSecretFailed(e)),
        },
        _ => return Ok(()),
    }
}

fn make_daemon_set_name(fb: &FluentBit) -> String {
    fb.metadata.name.as_ref().unwrap().clone()
}

fn make_daemon_set(fb: &FluentBit) -> DaemonSet {
    let labels = BTreeMap::from([(
        "app".to_string(),
        fb.metadata.name.as_ref().unwrap().clone(),
    )]);
    DaemonSet {
        metadata: ObjectMeta {
            name: Some(make_daemon_set_name(fb)),
            namespace: fb.metadata.namespace.clone(),
            labels: Some(labels.clone()),
            ..ObjectMeta::default()
        },
        spec: Some(appsv1::DaemonSetSpec {
            selector: metav1::LabelSelector {
                match_labels: Some(labels.clone()),
                ..metav1::LabelSelector::default()
            },
            template: corev1::PodTemplateSpec {
                metadata: Some(metav1::ObjectMeta {
                    name: Some(make_daemon_set_name(fb)),
                    namespace: fb.metadata.namespace.clone(),
                    labels: Some(labels.clone()),
                    ..ObjectMeta::default()
                }),
                spec: Some(corev1::PodSpec {
                    service_account_name: Some(make_service_account_name(fb)),
                    volumes: Some(vec![
                        corev1::Volume {
                            name: "varlibcontainers".to_string(),
                            host_path: Some(corev1::HostPathVolumeSource {
                                path: "/containers".to_string(),
                                ..corev1::HostPathVolumeSource::default()
                            }),
                            ..corev1::Volume::default()
                        },
                        corev1::Volume {
                            name: "config".to_string(),
                            secret: Some(corev1::SecretVolumeSource {
                                secret_name: Some(make_secret_name(fb)),
                                ..corev1::SecretVolumeSource::default()
                            }),
                            ..corev1::Volume::default()
                        },
                        corev1::Volume {
                            name: "varlogs".to_string(),
                            host_path: Some(corev1::HostPathVolumeSource {
                                path: "/var/log".to_string(),
                                ..corev1::HostPathVolumeSource::default()
                            }),
                            ..corev1::Volume::default()
                        },
                        corev1::Volume {
                            name: "systemd".to_string(),
                            host_path: Some(corev1::HostPathVolumeSource {
                                path: "/var/log/journal".to_string(),
                                ..corev1::HostPathVolumeSource::default()
                            }),
                            ..corev1::Volume::default()
                        },
                        corev1::Volume {
                            name: "positions".to_string(),
                            host_path: Some(corev1::HostPathVolumeSource {
                                path: "/var/lib/fluent-bit/".to_string(),
                                ..corev1::HostPathVolumeSource::default()
                            }),
                            ..corev1::Volume::default()
                        },
                    ]),
                    containers: vec![corev1::Container {
                        name: "fluent-bit".to_string(),
                        image: Some("kubesphere/fluent-bit:v2.1.7".to_string()),
                        ports: Some(vec![corev1::ContainerPort {
                            name: Some("metrics".to_string()),
                            container_port: 2020,
                            ..corev1::ContainerPort::default()
                        }]),
                        env: Some(vec![
                            corev1::EnvVar {
                                name: "NODE_NAME".to_string(),
                                value_from: Some(corev1::EnvVarSource {
                                    field_ref: Some(corev1::ObjectFieldSelector {
                                        field_path: "spec.nodeName".to_string(),
                                        ..corev1::ObjectFieldSelector::default()
                                    }),
                                    ..corev1::EnvVarSource::default()
                                }),
                                ..corev1::EnvVar::default()
                            },
                            corev1::EnvVar {
                                name: "HOST_IP".to_string(),
                                value_from: Some(corev1::EnvVarSource {
                                    field_ref: Some(corev1::ObjectFieldSelector {
                                        field_path: "status.hostIP".to_string(),
                                        ..corev1::ObjectFieldSelector::default()
                                    }),
                                    ..corev1::EnvVarSource::default()
                                }),
                                ..corev1::EnvVar::default()
                            },
                        ]),
                        volume_mounts: Some(vec![
                            corev1::VolumeMount {
                                name: "varlibcontainers".to_string(),
                                read_only: Some(true),
                                mount_path: "/containers".to_string(),
                                ..corev1::VolumeMount::default()
                            },
                            corev1::VolumeMount {
                                name: "config".to_string(),
                                read_only: Some(true),
                                mount_path: "/fluent-bit/config".to_string(),
                                ..corev1::VolumeMount::default()
                            },
                            corev1::VolumeMount {
                                name: "varlogs".to_string(),
                                read_only: Some(true),
                                mount_path: "/var/log/".to_string(),
                                ..corev1::VolumeMount::default()
                            },
                            corev1::VolumeMount {
                                name: "systemd".to_string(),
                                read_only: Some(true),
                                mount_path: "/var/log/journal".to_string(),
                                ..corev1::VolumeMount::default()
                            },
                            corev1::VolumeMount {
                                name: "positions".to_string(),
                                mount_path: "/fluent-bit/tail".to_string(),
                                ..corev1::VolumeMount::default()
                            },
                        ]),
                        ..corev1::Container::default()
                    }],
                    tolerations: Some(vec![corev1::Toleration {
                        operator: Some("Exists".to_string()),
                        ..corev1::Toleration::default()
                    }]),
                    ..corev1::PodSpec::default()
                }),
            },
            ..appsv1::DaemonSetSpec::default()
        }),
        ..DaemonSet::default()
    }
}

async fn reconcile_daemon_set(fb: &FluentBit, client: Client) -> Result<(), Error> {
    let ds_api =
        Api::<DaemonSet>::namespaced(client.clone(), fb.metadata.namespace.as_ref().unwrap());
    let daemon_set = make_daemon_set(&fb);
    info!(
        "Create daemon set: {}",
        daemon_set.metadata.name.as_ref().unwrap()
    );
    match ds_api.create(&PostParams::default(), &daemon_set).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" =>
            {
                return Ok(())
            }
            _ => return Err(Error::ReconcileDaemonSetFailed(e)),
        },
        _ => return Ok(()),
    }
}

// In the reference fluent-operator, there are multiple reconcile loops for manaing fluent-bit.
// One reconcile loop creates the configuration (the secret object) and the other one brings up the daemon set
// that requires the configuration data.
// Here we simplify the design and fold everything into one reconcile loop.
// TODO(xudong): implement multiple reconcile loops that coordinate with each other.
async fn reconcile(fb_from_cache: Arc<FluentBit>, ctx: Arc<Data>) -> Result<Action, Error> {
    let client = &ctx.client;

    let fb_name = fb_from_cache
        .metadata
        .name
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.name"))?;
    let fb_ns = fb_from_cache
        .metadata
        .namespace
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.namespace"))?;

    let fb_api = Api::<FluentBit>::namespaced(client.clone(), &fb_ns);

    // Get the FluentBit custom resource before taking any reconciliation actions.
    let get_result = fb_api.get(&fb_name).await;
    match get_result {
        Err(kube_client::error::Error::Api(kube_core::ErrorResponse { reason, .. }))
            if &reason == "NotFound" =>
        {
            info!("{} not found, end reconcile", fb_name);
            return Ok(Action::await_change());
        }
        Err(e) => return Err(Error::CRGetFailed(e)),
        _ => {}
    }
    let fb = get_result.unwrap();

    // The cluster role, service account and cluster role binding are used to grant access to reading the pods
    // to the fluent-bit processes (running as pods of the daemon set below).
    // Each fluent-bit pod needs such access because one of its filters (kubernetes) needs to query the API server
    // to get the pod information.
    reconcile_cluster_role(&fb, client.clone()).await?;
    reconcile_service_account(&fb, client.clone()).await?;
    reconcile_cluster_role_binding(&fb, client.clone()).await?;

    // The secret contains the configuration data, including the input, filters and the output.
    // TODO(xudong): see whether we can use configmap here
    reconcile_secret(&fb, client.clone()).await?;

    // The daemon set hosts the fluent-bit pods.
    // The daemon set controller will spawn one pod on each Kubernetes node
    // and each pod will collect the logs (configured in input)
    // and send them to Kafka (configured in output).
    reconcile_daemon_set(&fb, client.clone()).await?;

    Ok(Action::requeue(Duration::from_secs(60)))
}

fn error_policy(_object: Arc<FluentBit>, error: &Error, _ctx: Arc<Data>) -> Action {
    warn!("Reconcile failed due to error: {}", error);
    Action::requeue(Duration::from_secs(10))
}

struct Data {
    client: Client,
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();
    if cmd == String::from("export") {
        info!("exporting custom resource definition");
        println!("{}", serde_yaml::to_string(&FluentBit::crd())?);
    } else if cmd == String::from("run") {
        info!("running fluent-controller");
        let client = Client::try_default().await?;
        let zks = Api::<FluentBit>::all(client.clone());

        Controller::new(zks, ListParams::default())
            .shutdown_on_signal()
            .run(reconcile, error_policy, Arc::new(Data { client }))
            .for_each(|res| async move {
                match res {
                    Ok(o) => info!("reconciled {:?}", o),
                    Err(e) => warn!("reconcile failed: {}", e),
                }
            })
            .await;
        info!("controller terminated");
    } else {
        warn!("wrong command; please use \"export\" or \"run\"");
    }
    Ok(())
}
