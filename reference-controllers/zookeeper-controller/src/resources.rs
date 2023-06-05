use k8s_openapi::api::apps::v1 as appsv1;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as metav1;
use kube::api::{ObjectMeta, Resource};
use std::{collections::BTreeMap, vec};

use crate::common::*;
use crate::zookeepercluster_types::*;

pub fn make_statefulset(zk: &ZookeeperCluster) -> appsv1::StatefulSet {
    appsv1::StatefulSet {
        metadata: ObjectMeta {
            name: Some(stateful_set_name(zk)),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                zk.meta().name.as_ref().unwrap().clone(),
            )])),
            ..ObjectMeta::default()
        },
        spec: Some(appsv1::StatefulSetSpec {
            replicas: Some(zk.spec.replica),
            service_name: headless_service_name(zk),
            selector: metav1::LabelSelector {
                match_labels: Some(BTreeMap::from([(
                    "app".to_string(),
                    zk.meta().name.as_ref().unwrap().clone(),
                )])),
                ..metav1::LabelSelector::default()
            },
            persistent_volume_claim_retention_policy: Some(
                appsv1::StatefulSetPersistentVolumeClaimRetentionPolicy {
                    when_deleted: Some("Delete".to_string()),
                    when_scaled: Some("Delete".to_string()),
                },
            ),
            template: corev1::PodTemplateSpec {
                metadata: Some(metav1::ObjectMeta {
                    generate_name: zk.meta().name.clone(),
                    labels: Some(BTreeMap::from([
                        ("app".to_string(), zk.meta().name.as_ref().unwrap().clone()),
                        ("kind".to_string(), "ZookeeperMember".to_string()),
                    ])),
                    ..metav1::ObjectMeta::default()
                }),
                spec: Some(make_zk_pod_spec(zk)),
            },
            volume_claim_templates: Some(vec![corev1::PersistentVolumeClaim {
                metadata: metav1::ObjectMeta {
                    name: Some("data".to_string()),
                    labels: Some(BTreeMap::from([(
                        "app".to_string(),
                        zk.meta().name.as_ref().unwrap().clone(),
                    )])),
                    ..metav1::ObjectMeta::default()
                },
                spec: Some(corev1::PersistentVolumeClaimSpec {
                    access_modes: Some(vec!["ReadWriteOnce".to_string()]),
                    resources: Some(corev1::ResourceRequirements {
                        requests: Some(BTreeMap::from([(
                            "storage".to_string(),
                            Quantity("20Gi".to_string()),
                        )])),
                        ..corev1::ResourceRequirements::default()
                    }),
                    ..corev1::PersistentVolumeClaimSpec::default()
                }),
                ..corev1::PersistentVolumeClaim::default()
            }]),
            ..appsv1::StatefulSetSpec::default()
        }),
        ..appsv1::StatefulSet::default()
    }
}

fn make_zk_pod_spec(zk: &ZookeeperCluster) -> corev1::PodSpec {
    corev1::PodSpec {
        containers: vec![corev1::Container {
            name: "zookeeper".to_string(),
            image: Some("pravega/zookeeper:0.2.14".to_string()),
            command: Some(vec!["/usr/local/bin/zookeeperStart.sh".to_string()]),
            image_pull_policy: Some("Always".to_string()),
            volume_mounts: Some(vec![
                corev1::VolumeMount {
                    name: "data".to_string(),
                    mount_path: "/data".to_string(),
                    ..corev1::VolumeMount::default()
                },
                corev1::VolumeMount {
                    name: "conf".to_string(),
                    mount_path: "/conf".to_string(),
                    ..corev1::VolumeMount::default()
                },
            ]),
            ports: Some(vec![
                corev1::ContainerPort {
                    name: Some("client".to_string()),
                    container_port: 2181,
                    ..corev1::ContainerPort::default()
                },
                corev1::ContainerPort {
                    name: Some("quorum".to_string()),
                    container_port: 2888,
                    ..corev1::ContainerPort::default()
                },
                corev1::ContainerPort {
                    name: Some("leader-election".to_string()),
                    container_port: 3888,
                    ..corev1::ContainerPort::default()
                },
                corev1::ContainerPort {
                    name: Some("metrics".to_string()),
                    container_port: 7000,
                    ..corev1::ContainerPort::default()
                },
                corev1::ContainerPort {
                    name: Some("admin-server".to_string()),
                    container_port: 8080,
                    ..corev1::ContainerPort::default()
                },
            ]),
            readiness_probe: Some(corev1::Probe {
                exec: Some(corev1::ExecAction {
                    command: Some(vec!["zookeeperReady.sh".to_string()]),
                }),
                failure_threshold: Some(3),
                initial_delay_seconds: Some(10),
                period_seconds: Some(10),
                success_threshold: Some(1),
                timeout_seconds: Some(10),
                ..corev1::Probe::default()
            }),
            liveness_probe: Some(corev1::Probe {
                exec: Some(corev1::ExecAction {
                    command: Some(vec!["zookeeperLive.sh".to_string()]),
                }),
                failure_threshold: Some(3),
                initial_delay_seconds: Some(10),
                period_seconds: Some(10),
                success_threshold: Some(1),
                timeout_seconds: Some(10),
                ..corev1::Probe::default()
            }),
            ..corev1::Container::default()
        }],
        volumes: Some(vec![corev1::Volume {
            name: "conf".to_string(),
            config_map: Some(corev1::ConfigMapVolumeSource {
                name: Some(zk.meta().name.as_ref().unwrap().clone() + "-configmap"),
                ..corev1::ConfigMapVolumeSource::default()
            }),
            ..corev1::Volume::default()
        }]),
        ..corev1::PodSpec::default()
    }
}

pub fn make_headless_service(zk: &ZookeeperCluster) -> corev1::Service {
    make_service(
        zk,
        headless_service_name(zk),
        vec![
            corev1::ServicePort {
                name: Some("tcp-client".to_string()),
                port: 2181,
                ..corev1::ServicePort::default()
            },
            corev1::ServicePort {
                name: Some("tcp-quorum".to_string()),
                port: 2888,
                ..corev1::ServicePort::default()
            },
            corev1::ServicePort {
                name: Some("tcp-leader-election".to_string()),
                port: 3888,
                ..corev1::ServicePort::default()
            },
            corev1::ServicePort {
                name: Some("tcp-metrics".to_string()),
                port: 7000,
                ..corev1::ServicePort::default()
            },
            corev1::ServicePort {
                name: Some("tcp-admin-server".to_string()),
                port: 8080,
                ..corev1::ServicePort::default()
            },
        ],
        false,
    )
}

pub fn make_client_service(zk: &ZookeeperCluster) -> corev1::Service {
    make_service(
        zk,
        client_service_name(zk),
        vec![corev1::ServicePort {
            name: Some("tcp-client".to_string()),
            port: 2181,
            ..corev1::ServicePort::default()
        }],
        true,
    )
}

pub fn make_admin_server_service(zk: &ZookeeperCluster) -> corev1::Service {
    make_service(
        zk,
        admin_server_service_name(zk),
        vec![corev1::ServicePort {
            name: Some("tcp-admin-server".to_string()),
            port: 8080,
            ..corev1::ServicePort::default()
        }],
        true,
    )
}

fn make_service(
    zk: &ZookeeperCluster,
    name: String,
    ports: Vec<corev1::ServicePort>,
    cluster_ip: bool,
) -> corev1::Service {
    corev1::Service {
        metadata: ObjectMeta {
            name: Some(name),
            owner_references: Some(vec![zk.controller_owner_ref(&()).unwrap()]),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                zk.meta().name.as_ref().unwrap().clone(),
            )])),
            ..ObjectMeta::default()
        },
        spec: Some(corev1::ServiceSpec {
            cluster_ip: if !cluster_ip {
                Some("None".to_string())
            } else {
                None
            },
            ports: Some(ports),
            selector: Some(BTreeMap::from([(
                "app".to_string(),
                zk.meta().name.as_ref().unwrap().clone(),
            )])),
            ..corev1::ServiceSpec::default()
        }),
        ..corev1::Service::default()
    }
}

pub fn make_configmap(zk: &ZookeeperCluster) -> corev1::ConfigMap {
    corev1::ConfigMap {
        metadata: ObjectMeta {
            name: Some(config_map_name(zk)),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                zk.meta().name.as_ref().unwrap().clone(),
            )])),
            owner_references: Some(vec![zk.controller_owner_ref(&()).unwrap()]),
            ..ObjectMeta::default()
        },
        data: Some(BTreeMap::from([
            ("zoo.cfg".to_string(), make_zk_config()),
            ("log4j.properties".to_string(), make_log4j_config()),
            (
                "log4j-quiet.properties".to_string(),
                make_log4j_quiet_config(),
            ),
            ("env.sh".to_string(), make_env_config(zk)),
        ])),
        ..corev1::ConfigMap::default()
    }
}

fn make_zk_config() -> String {
    concat!(
        "4lw.commands.whitelist=cons, envi, conf, crst, srvr, stat, mntr, ruok\n",
        "dataDir=/data\n",
        "standaloneEnabled=false\n",
        "reconfigEnabled=true\n",
        "skipACL=yes\n",
        "metricsProvider.className=org.apache.zookeeper.metrics.prometheus.PrometheusMetricsProvider\n",
        "metricsProvider.httpPort=7000\n",
        "metricsProvider.exportJvmInfo=true\n",
        "initLimit=10\n",
        "syncLimit=2\n",
        "tickTime=2000\n",
        "globalOutstandingLimit=1000\n",
        "preAllocSize=65536\n",
        "snapCount=10000\n",
        "commitLogCount=500\n",
        "snapSizeLimitInKb=4194304\n",
        "maxCnxns=0\n",
        "maxClientCnxns=60\n",
        "minSessionTimeout=4000\n",
        "maxSessionTimeout=40000\n",
        "autopurge.snapRetainCount=3\n",
        "autopurge.purgeInterval=1\n",
        "quorumListenOnAllIPs=false\n",
        "admin.serverPort=8080\n",
        "dynamicConfigFile=/data/zoo.cfg.dynamic\n"
    ).to_string()
}

fn make_log4j_config() -> String {
    concat!(
        "zookeeper.root.logger=CONSOLE\n",
	    "zookeeper.console.threshold=INFO\n",
	    "log4j.rootLogger=${zookeeper.root.logger}\n",
	    "log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n",
	    "log4j.appender.CONSOLE.Threshold=${zookeeper.console.threshold}\n",
	    "log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n",
	    "log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    ).to_string()
}

fn make_log4j_quiet_config() -> String {
    concat!(
        "log4j.rootLogger=ERROR, CONSOLE\n",
        "log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n",
        "log4j.appender.CONSOLE.Threshold=ERROR\n",
        "log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n",
        "log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    ).to_string()
}

fn make_env_config(zk: &ZookeeperCluster) -> String {
    format!(
        "#!/usr/bin/env bash\n\n\
        DOMAIN={name}-headless.{namespace}.svc.cluster.local\n\
        QUORUM_PORT=2888\n\
        LEADER_PORT=3888\n\
        CLIENT_HOST={name}-client\n\
        CLIENT_PORT=2181\n\
        ADMIN_SERVER_HOST={name}-admin-server\n\
        ADMIN_SERVER_PORT=8080\n\
        CLUSTER_NAME={name}\n\
        CLUSTER_SIZE={replica}\n",
        name = zk.meta().name.as_ref().unwrap().clone(),
        namespace = zk.meta().namespace.as_ref().unwrap().clone(),
        replica = zk.spec.replica
    )
}
