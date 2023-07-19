use k8s_openapi::api::apps::v1 as appsv1;
use k8s_openapi::api::core::v1 as corev1;
use k8s_openapi::api::rbac::v1 as rbacv1;
use k8s_openapi::apimachinery::pkg::api::resource as k8sresource;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as metav1;
use kube::{
    api::{Api, ListParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_client::{self, client};
use kube_core::{self, Resource};
use std::collections::BTreeMap;
use crate::{rabbitmqcluster_types::RabbitmqCluster, Error};
use k8s_openapi::apimachinery::pkg::util::intstr::IntOrString as IntOrString;



pub fn statefulset_build( rabbitmq: &RabbitmqCluster) -> appsv1::StatefulSet {
    let sts_name = rabbitmq.metadata.name.clone().unwrap() + "-server";
    let headless_name = rabbitmq.metadata.name.clone().unwrap() + "-nodes";

    let pvc = persistent_volume_claim(rabbitmq);

    // update_persistence_storage_capacity(&mut pvc, rabbitmq.spec.persistence.as_ref().unwrap().storage.as_ref().unwrap());

    let sts = appsv1::StatefulSet{
        metadata: metav1::ObjectMeta {
            name: Some(sts_name.clone()),
            namespace: rabbitmq.meta().namespace.clone(),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            ..metav1::ObjectMeta::default()
        },
        spec: Some(appsv1::StatefulSetSpec{
            service_name: headless_name.clone(),
            replicas: Some(rabbitmq.spec.replicas),
            update_strategy: Some(appsv1::StatefulSetUpdateStrategy{
                type_: Some("RollingUpdate".to_string()),
                rolling_update: Some(appsv1::RollingUpdateStatefulSetStrategy{
                    partition: Some(0),
                    ..appsv1::RollingUpdateStatefulSetStrategy::default()
                }),
            }),
            selector: metav1::LabelSelector{
                match_labels: Some(BTreeMap::from([(
                    "app".to_string(),
                    rabbitmq.meta().name.as_ref().unwrap().clone(),
                )])),
                ..metav1::LabelSelector::default()
            },
            volume_claim_templates: Some(pvc),
            pod_management_policy: Some("Parallel".to_string()),
            template: pod_template_spec(rabbitmq),
            ..appsv1::StatefulSetSpec::default()
        }),
        ..appsv1::StatefulSet::default()
    };
    sts
}

fn persistent_volume_claim(rabbitmq: &RabbitmqCluster) ->Vec<corev1::PersistentVolumeClaim>{
    let mut pvc = Vec::new();
    let pvc_data = corev1::PersistentVolumeClaim {
        metadata: metav1::ObjectMeta {
            name: Some("persistence".to_string()),
            namespace: rabbitmq.meta().namespace.clone(),
            owner_references: Some(vec![rabbitmq.controller_owner_ref(&()).unwrap()]),
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            ..metav1::ObjectMeta::default()
        },
        spec: Some(corev1::PersistentVolumeClaimSpec{
            resources: Some(corev1::ResourceRequirements {
                requests: Some(BTreeMap::from([(
                    "storage".to_string(),
                    k8sresource::Quantity("10Gi".to_string()),
                )])),
                ..corev1::ResourceRequirements::default()
            }),
            access_modes: Some(vec!["ReadWriteOnce".to_string()]),
            ..corev1::PersistentVolumeClaimSpec::default()
        }),
        ..corev1::PersistentVolumeClaim::default()
    };
    pvc.push(pvc_data);
    pvc
}



fn pod_template_spec(rabbitmq: &RabbitmqCluster) -> corev1::PodTemplateSpec{
    let readiness_probe_port = "amqp".to_string(); // default one
    let volumes = vec![
            corev1::Volume{          
                name: "plugins-conf".to_string(),
                config_map: Some(corev1::ConfigMapVolumeSource{
                    name: Some(rabbitmq.metadata.name.clone().unwrap() + "-plugins-conf"),
                    ..corev1::ConfigMapVolumeSource::default()
                }),
                ..corev1::Volume::default()
            },
            corev1::Volume{
                name:"rabbitmq-confd".to_string(),
                projected: Some(corev1::ProjectedVolumeSource{
                    sources: Some(vec![
                        corev1::VolumeProjection{
                            config_map: Some(corev1::ConfigMapProjection{
                                name: Some(rabbitmq.metadata.name.clone().unwrap() + "-server-conf"),
                                items: Some(vec![
                                    corev1::KeyToPath{
                                        key: "operatorDefaults.conf".to_string(),
                                        path: "operatorDefaults.conf".to_string(),
                                        ..corev1::KeyToPath::default()
                                    },
                                    corev1::KeyToPath{
                                        key: "userDefinedConfiguration.conf".to_string(),
                                        path: "userDefinedConfiguration.conf".to_string(),
                                        ..corev1::KeyToPath::default()
                                    }
                                ]),
                                ..corev1::ConfigMapProjection::default()
                            }),
                            ..corev1::VolumeProjection::default()
                        },
                        corev1::VolumeProjection{
                            secret: Some(corev1::SecretProjection{
                                name: Some(rabbitmq.metadata.name.clone().unwrap() + "-default-user"),
                                items: Some(vec![
                                    corev1::KeyToPath{
                                        key: "default_user.conf".to_string(),
                                        path: "default_user.conf".to_string(),
                                        ..corev1::KeyToPath::default()
                                    },
                                ]),
                                ..corev1::SecretProjection::default()
                            }),
                            ..corev1::VolumeProjection::default()
                        }
                    ]),
                    ..corev1::ProjectedVolumeSource::default()
                }),
                ..corev1::Volume::default()
            },
            corev1::Volume{
                name:"rabbitmq-erlang-cookie".to_string(),
                empty_dir: Some(corev1::EmptyDirVolumeSource{ ..corev1::EmptyDirVolumeSource::default() }),
                ..corev1::Volume::default()
            },
            corev1::Volume{
                name:"erlang-cookie-secret".to_string(),
                secret: Some(corev1::SecretVolumeSource{
                    secret_name: Some(rabbitmq.metadata.name.clone().unwrap() + "-erlang-cookie"),
                    ..corev1::SecretVolumeSource::default()
                }),
                ..corev1::Volume::default()
            },
            corev1::Volume{
                name:"rabbitmq-plugins".to_string(),
                empty_dir: Some(corev1::EmptyDirVolumeSource{ ..corev1::EmptyDirVolumeSource::default() }),
                ..corev1::Volume::default()
            },
            corev1::Volume{
                name: "pod-info".to_string(),
                downward_api: Some(corev1::DownwardAPIVolumeSource{
                    items: Some(vec![
                        corev1::DownwardAPIVolumeFile{
                            path: "skipPreStopChecks".to_string(),
                            field_ref: Some(corev1::ObjectFieldSelector{
                                field_path: "metadata.labels['skipPreStopChecks']".to_string(),
                                ..corev1::ObjectFieldSelector::default()
                            }),
                            ..corev1::DownwardAPIVolumeFile::default()
                            },   
                        ]),
                    ..corev1::DownwardAPIVolumeSource::default()
                }),
                ..corev1::Volume::default()
            }
    ];

    let rbmq_container_volume_mounts = vec![
        corev1::VolumeMount{
            name: "rabbitmq-erlang-cookie".to_string(),
            mount_path: "/var/lib/rabbitmq/".to_string(),
            ..corev1::VolumeMount::default()
        },
        corev1::VolumeMount{
            name: "persistence".to_string(),
            mount_path: "/var/lib/rabbitmq/mnesia/".to_string(),
            ..corev1::VolumeMount::default()
        },
        corev1::VolumeMount{
            name: "rabbitmq-plugins".to_string(),
            mount_path: "/operator".to_string(),
            ..corev1::VolumeMount::default()
        },
        corev1::VolumeMount{
            name: "rabbitmq-confd".to_string(),
            mount_path: "/etc/rabbitmq/conf.d/10-operatorDefaults.conf".to_string(),
            sub_path: Some("operatorDefaults.conf".to_string()),
            ..corev1::VolumeMount::default()
        },
        corev1::VolumeMount{
            name: "rabbitmq-confd".to_string(),
            mount_path: "/etc/rabbitmq/conf.d/90-userDefinedConfiguration.conf".to_string(),
            sub_path: Some("userDefinedConfiguration.conf".to_string()),
            ..corev1::VolumeMount::default()
        },
        corev1::VolumeMount{
            name: "pod-info".to_string(),
            mount_path: "/etc/pod-info/".to_string(),
            ..corev1::VolumeMount::default()
        },
        corev1::VolumeMount{
            name: "rabbitmq-confd".to_string(),
            mount_path: "/etc/rabbitmq/conf.d/11-default_user.conf".to_string(),
            sub_path: Some("default_user.conf".to_string()),
            ..corev1::VolumeMount::default()
        },
    ];

    let mut image_used = Some(String::from("rabbitmq:3.11.10-management"));
    if rabbitmq.spec.image.is_some() {
        image_used = rabbitmq.spec.image.clone();
    }

    let rabbitmq_uid = 999 as i64;
    let pod_template_spec = corev1::PodTemplateSpec{
        metadata: Some(metav1::ObjectMeta{
            labels: Some(BTreeMap::from([(
                "app".to_string(),
                rabbitmq.meta().name.as_ref().unwrap().clone(),
            )])),
            ..metav1::ObjectMeta::default()
        }),
        spec: Some(corev1::PodSpec{
            topology_spread_constraints: Some(vec![
                corev1::TopologySpreadConstraint {
                    max_skew: 1,
                    topology_key: "topology.kubernetes.io/zone".to_string(),
                    when_unsatisfiable: "ScheduleAnyway".to_string(),
                    ..Default::default()
                },
            ]),
            security_context: Some(corev1::PodSecurityContext {
                fs_group: Some(0),
                run_as_user: Some(rabbitmq_uid),
                ..Default::default()
            }),
            termination_grace_period_seconds: Some(604800), // default value
            service_account_name: Some(rabbitmq.meta().name.as_ref().unwrap().clone() + "-server"),
            automount_service_account_token: Some(true),
            init_containers: Some(vec![setup_container(&rabbitmq)]),
            volumes: Some(volumes),
            containers: vec![
                corev1::Container{
                    name: "rabbitmq".to_string(),
                    resources: Some(
                        corev1::ResourceRequirements{
                            requests: Some(
                                BTreeMap::from([
                                    ("cpu".to_string(), k8sresource::Quantity("1000m".to_string())),
                                    ("memory".to_string(), k8sresource::Quantity("2Gi".to_string()))
                                ])
                            ),
                            limits: Some(
                                BTreeMap::from([
                                    ("cpu".to_string(), k8sresource::Quantity("2000m".to_string())),
                                    ("memory".to_string(), k8sresource::Quantity("2Gi".to_string()))
                                ])
                            ),
                            ..Default::default()
                        }
                    ),
                    image:  image_used,
                    env: Some(make_env_vars(rabbitmq)),
                    ports: Some(make_container_ports(rabbitmq)),
                    volume_mounts: Some(rbmq_container_volume_mounts),
                    readiness_probe: Some(corev1::Probe{
                        initial_delay_seconds: Some(50),
                        timeout_seconds: Some(5),
                        period_seconds: Some(10),
                        failure_threshold: Some(3),
                        success_threshold: Some(1),
                        tcp_socket: Some(corev1::TCPSocketAction{
                            port:  IntOrString::String(readiness_probe_port),
                            ..Default::default()
                        }),
                        ..Default::default()
                    }),
                    lifecycle: Some(corev1::Lifecycle {
                        pre_stop: Some(corev1::LifecycleHandler{
                            exec: Some(corev1::ExecAction{
                                command: Some(vec![
                                    "sh".to_string(),
                                    "-c".to_string(),
                                    format!(
                                        "if [ ! -z \"$(cat /etc/pod-info/skipPreStopChecks)\" ]; then exit 0; fi; rabbitmq-upgrade await_online_quorum_plus_one -t {}; rabbitmq-upgrade await_online_synchronized_mirror -t {}; rabbitmq-upgrade drain -t {}",
                                        604800,
                                        604800,
                                        604800
                                    ),
                                ]),
                                ..Default::default()
                            }),
                            ..Default::default()
                        }),
                        ..Default::default()
                     }),
                    
                    ..Default::default()
                }
            ],
            ..Default::default()
        }),
        ..corev1::PodTemplateSpec::default()
    };
    pod_template_spec
}

fn setup_container(rabbitmq: &RabbitmqCluster) -> corev1::Container{
    let cpu_request = "100m".to_string();
    let mem_request = "500Mi".to_string();
    let command = vec![
        "sh".to_string(),
        "-c".to_string(),
        "cp /tmp/erlang-cookie-secret/.erlang.cookie /var/lib/rabbitmq/.erlang.cookie && chmod 600 /var/lib/rabbitmq/.erlang.cookie ; cp /tmp/rabbitmq-plugins/enabled_plugins /operator/enabled_plugins ; echo '[default]' > /var/lib/rabbitmq/.rabbitmqadmin.conf && sed -e 's/default_user/username/' -e 's/default_pass/password/' /tmp/default_user.conf >> /var/lib/rabbitmq/.rabbitmqadmin.conf && chmod 600 /var/lib/rabbitmq/.rabbitmqadmin.conf ; sleep 30".to_string() // default value

    ];

    let mut image_used = Some(String::from("rabbitmq:3.11.10-management"));
    if rabbitmq.spec.image.is_some() {
        image_used = rabbitmq.spec.image.clone();
    }
    let setup_container = corev1::Container {
        name: "setup-container".to_string(),
        image: image_used,
        command: Some(command),
        resources: Some(corev1::ResourceRequirements {
            limits: Some(
                BTreeMap::from([
                    ("cpu".to_string(), k8sresource::Quantity(cpu_request.clone())),
                    ("memory".to_string(), k8sresource::Quantity(mem_request.clone()))
                ])
            ),
            requests: Some(
                BTreeMap::from([
                    ("cpu".to_string(), k8sresource::Quantity(cpu_request.clone())),
                    ("memory".to_string(), k8sresource::Quantity(mem_request.clone()))
                ])
            ),
            ..corev1::ResourceRequirements::default()
        }),
        volume_mounts: Some(vec![
            corev1::VolumeMount {
                name: "plugins-conf".to_string(),
                mount_path: "/tmp/rabbitmq-plugins/".to_string(),
                ..Default::default()
            },
            corev1::VolumeMount {
                name: "rabbitmq-erlang-cookie".to_string(),
                mount_path: "/var/lib/rabbitmq/".to_string(),
                ..Default::default()
            },
            corev1::VolumeMount {
                name: "erlang-cookie-secret".to_string(),
                mount_path: "/tmp/erlang-cookie-secret/".to_string(),
                ..Default::default()
            },
            corev1::VolumeMount {
                name: "rabbitmq-plugins".to_string(),
                mount_path: "/operator".to_string(),
                ..Default::default()
            },
            corev1::VolumeMount {
                name: "persistence".to_string(),
                mount_path: "/var/lib/rabbitmq/mnesia/".to_string(),
                ..Default::default()
            },
            corev1::VolumeMount {
                name: "rabbitmq-confd".to_string(),
                mount_path: "/tmp/default_user.conf".to_string(),
                sub_path: Some("default_user.conf".to_string()),
                ..Default::default()
            },
        ]),
        ..Default::default()
    };


    setup_container
}


fn make_env_vars(rabbitmq: &RabbitmqCluster) -> Vec<corev1::EnvVar>{
    vec![
        corev1::EnvVar{
            name: "MY_POD_NAME".to_string(),
            value_from: Some(corev1::EnvVarSource{
                field_ref: Some(corev1::ObjectFieldSelector{
                    field_path: "metadata.name".to_string(),
                    api_version: Some("v1".to_string()),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            ..Default::default()
        },
        corev1::EnvVar{
            name: "MY_POD_NAMESPACE".to_string(),
            value_from: Some(corev1::EnvVarSource{
                field_ref: Some(corev1::ObjectFieldSelector{
                    field_path: "metadata.namespace".to_string(),
                    api_version: Some("v1".to_string()),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            ..Default::default()
        },
        corev1::EnvVar{
            name: "K8S_SERVICE_NAME".to_string(),
            value: Some(rabbitmq.metadata.name.clone().unwrap() + "-nodes"),
            ..Default::default()
        },              
        corev1::EnvVar {
            name: "RABBITMQ_ENABLED_PLUGINS_FILE".to_string(),
            value: Some("/operator/enabled_plugins".to_string()),
            ..Default::default()
        },
        corev1::EnvVar {
            name: "RABBITMQ_USE_LONGNAME".to_string(),
            value: Some("true".to_string()),
            ..Default::default()
        },
        corev1::EnvVar {
            name: "RABBITMQ_NODENAME".to_string(),
            value: Some("rabbit@$(MY_POD_NAME).$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)".to_string()),
            ..Default::default()
        },
        corev1::EnvVar {
            name: "K8S_HOSTNAME_SUFFIX".to_string(),
            value: Some(".$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)".to_string()),
            ..Default::default()
        },
    ]
}


fn make_container_ports(_rabbitmq: &RabbitmqCluster) -> Vec<corev1::ContainerPort>{
    vec![
        corev1::ContainerPort {
            container_port: 4369,
            name: Some("epmd".to_string()),
            ..Default::default()
        },
        corev1::ContainerPort {
            container_port: 5672,
            name: Some("amqp".to_string()),
            ..Default::default()
        },
        corev1::ContainerPort {
            container_port: 15672,
            name: Some("management".to_string()),
            ..Default::default()
        },
    ]
}
