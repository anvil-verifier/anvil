// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_examples::zookeeper_controller::common::*;
use crate::controller_examples::zookeeper_controller::spec::reconciler as zk_spec;
use crate::controller_examples::zookeeper_controller::spec::zookeepercluster::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, label_selector::*, object_meta::*,
    persistent_volume_claim::*, pod::*, pod_template_spec::*, resource_requirements::*, service::*,
    stateful_set::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::reconciler::exec::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;
use vstd::vec::*;

verus! {

/// ZookeeperReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct ZookeeperReconcileState {
    // reconcile_step, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_step: ZookeeperReconcileStep,

    // The custom resource object that the controller is currently reconciling for
    pub zk: Option<ZookeeperCluster>,
}

impl ZookeeperReconcileState {
    pub open spec fn to_view(&self) -> zk_spec::ZookeeperReconcileState {
        zk_spec::ZookeeperReconcileState {
            reconcile_step: self.reconcile_step,
            zk: match self.zk {
                Option::Some(inner_zk) => Option::Some(inner_zk@),
                Option::None => Option::None,
            }
        }
    }
}

pub struct ZookeeperReconciler {}

#[verifier(external)]
impl Reconciler<ZookeeperReconcileState> for ZookeeperReconciler {
    fn reconcile_init_state(&self) -> ZookeeperReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, zk_ref: &KubeObjectRef, resp_o: Option<KubeAPIResponse>, state: ZookeeperReconcileState) -> (ZookeeperReconcileState, Option<KubeAPIRequest>) {
        reconcile_core(zk_ref, resp_o, state)
    }

    fn reconcile_done(&self, state: &ZookeeperReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(&self, state: &ZookeeperReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for ZookeeperReconciler {
    fn default() -> ZookeeperReconciler { ZookeeperReconciler{} }
}

pub fn reconcile_init_state() -> (state: ZookeeperReconcileState)
    ensures
        state.to_view() == zk_spec::reconcile_init_state(),
{
    ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Init,
        zk: Option::None,
    }
}

pub fn reconcile_done(state: &ZookeeperReconcileState) -> (res: bool)
    ensures
        res == zk_spec::reconcile_done(state.to_view()),
{
    match state.reconcile_step {
        ZookeeperReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &ZookeeperReconcileState) -> (res: bool)
    ensures
        res == zk_spec::reconcile_error(state.to_view()),
{
    match state.reconcile_step {
        ZookeeperReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(zk_ref: &KubeObjectRef, resp_o: Option<KubeAPIResponse>, state: ZookeeperReconcileState) -> (res: (ZookeeperReconcileState, Option<KubeAPIRequest>))
    requires
        zk_ref.kind.is_CustomResourceKind(),
    ensures
        (res.0.to_view(), opt_req_to_view(&res.1)) == zk_spec::reconcile_core(zk_ref.to_view(), opt_resp_to_view(&resp_o), state.to_view()),
{
    let step = state.reconcile_step;
    match step {
        ZookeeperReconcileStep::Init => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterGetZK,
                ..state
            };
            let req_o = Option::Some(KubeAPIRequest::GetRequest(
                KubeGetRequest {
                    api_resource: ZookeeperCluster::api_resource(),
                    name: zk_ref.name.clone(),
                    namespace: zk_ref.namespace.clone(),
                }
            ));
            (state_prime, req_o)
        },
        ZookeeperReconcileStep::AfterGetZK => {
            if !resp_o.is_some() {
                return (ZookeeperReconcileState { reconcile_step: ZookeeperReconcileStep::Error, ..state }, Option::None);
            }
            let resp = resp_o.unwrap();
            if !(resp.is_get_response() && resp.as_get_response_ref().res.is_ok()) {
                return (ZookeeperReconcileState { reconcile_step: ZookeeperReconcileStep::Error, ..state }, Option::None);
            }
            let zk = ZookeeperCluster::from_dynamic_object(resp.into_get_response().res.unwrap());
            if !(zk.name().is_some() && zk.namespace().is_some()) {
                return (ZookeeperReconcileState { reconcile_step: ZookeeperReconcileStep::Error, ..state }, Option::None);
            }
            let headless_service = make_headless_service(&zk);
            let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                KubeCreateRequest {
                    api_resource: Service::api_resource(),
                    obj: headless_service.to_dynamic_object(),
                }
            ));
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateHeadlessService,
                zk: Option::Some(zk),
                ..state
            };
            return (state_prime, req_o);
        },
        ZookeeperReconcileStep::AfterCreateHeadlessService => {
            if !state.zk.is_some() {
                return (ZookeeperReconcileState { reconcile_step: ZookeeperReconcileStep::Error, ..state }, Option::None);
            }
            let zk = state.zk.as_ref().unwrap();
            if !(zk.name().is_some() && zk.namespace().is_some()) {
                return (ZookeeperReconcileState { reconcile_step: ZookeeperReconcileStep::Error, ..state }, Option::None);
            }
            let client_service = make_client_service(zk);
            let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                KubeCreateRequest {
                    api_resource: Service::api_resource(),
                    obj: client_service.to_dynamic_object(),
                }
            ));
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateClientService,
                ..state
            };
            return (state_prime, req_o);
        },
        ZookeeperReconcileStep::AfterCreateClientService => {
            if !state.zk.is_some() {
                return (ZookeeperReconcileState { reconcile_step: ZookeeperReconcileStep::Error, ..state }, Option::None);
            }
            let zk = state.zk.as_ref().unwrap();
            if !(zk.name().is_some() && zk.namespace().is_some()) {
                return (ZookeeperReconcileState { reconcile_step: ZookeeperReconcileStep::Error, ..state }, Option::None);
            }
            let admin_server_service = make_admin_server_service(zk);
            let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                KubeCreateRequest {
                    api_resource: Service::api_resource(),
                    obj: admin_server_service.to_dynamic_object(),
                }
            ));
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateAdminServerService,
                ..state
            };
            return (state_prime, req_o);
        },
        ZookeeperReconcileStep::AfterCreateAdminServerService => {
            if !state.zk.is_some() {
                return (ZookeeperReconcileState { reconcile_step: ZookeeperReconcileStep::Error, ..state }, Option::None);
            }
            let zk = state.zk.as_ref().unwrap();
            if !(zk.name().is_some() && zk.namespace().is_some()) {
                return (ZookeeperReconcileState { reconcile_step: ZookeeperReconcileStep::Error, ..state }, Option::None);
            }
            let configmap = make_configmap(zk);
            let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                KubeCreateRequest {
                    api_resource: ConfigMap::api_resource(),
                    obj: configmap.to_dynamic_object(),
                }
            ));
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Done,
                ..state
            };
            return (state_prime, req_o);
        },
        _ => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = Option::None;
            (state_prime, req_o)
        }
    }
}

fn make_headless_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
    ensures
        service@ == zk_spec::make_headless_service(zk@),
{
    let mut ports = Vec::empty();

    ports.push(ServicePort::new_with(new_strlit("tcp-client").to_string(), 2181));
    ports.push(ServicePort::new_with(new_strlit("tcp-quorum").to_string(), 2888));
    ports.push(ServicePort::new_with(new_strlit("tcp-leader-election").to_string(), 3888));
    ports.push(ServicePort::new_with(new_strlit("tcp-metrics").to_string(), 7000));
    ports.push(ServicePort::new_with(new_strlit("tcp-admin-server").to_string(), 8080));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_headless_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, zk.name().unwrap().concat(new_strlit("-headless")), ports, false)
}

fn make_client_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
    ensures
        service@ == zk_spec::make_client_service(zk@),
{
    let mut ports = Vec::empty();

    ports.push(ServicePort::new_with(new_strlit("tcp-client").to_string(), 2181));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_client_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, zk.name().unwrap().concat(new_strlit("-client")), ports, true)
}

fn make_admin_server_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
    ensures
        service@ == zk_spec::make_admin_server_service(zk@),
{
    let mut ports = Vec::empty();

    ports.push(ServicePort::new_with(new_strlit("tcp-admin-server").to_string(), 8080));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_admin_server_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, zk.name().unwrap().concat(new_strlit("-admin-server")), ports, true)
}

fn make_service(zk: &ZookeeperCluster, name: String, ports: Vec<ServicePort>, cluster_ip: bool) -> (service: Service)
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
    ensures
        service@ == zk_spec::make_service(zk@, name@, ports@.map_values(|port: ServicePort| port@), cluster_ip),
{
    let mut metadata = ObjectMeta::default();
    metadata.set_name(name);
    metadata.set_namespace(zk.namespace().unwrap());
    let mut labels = StringMap::empty();
    labels.insert(new_strlit("app").to_string(), zk.name().unwrap());
    metadata.set_labels(labels);

    let mut service_spec = ServiceSpec::default();
    if !cluster_ip {
        service_spec.set_cluster_ip(new_strlit("None").to_string());
    }
    service_spec.set_ports(ports);
    let mut selector = StringMap::empty();
    selector.insert(new_strlit("app").to_string(), zk.name().unwrap());
    service_spec.set_selector(selector);

    let mut service = Service::default();
    service.set_metadata(metadata);
    service.set_spec(service_spec);

    service
}

fn make_configmap(zk: &ZookeeperCluster) -> (configmap: ConfigMap)
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
    ensures
        configmap@ == zk_spec::make_configmap(zk@),
{
    let mut configmap = ConfigMap::default();
    configmap.set_name(zk.name().unwrap().concat(new_strlit("-configmap")));
    configmap.set_namespace(zk.namespace().unwrap());

    let mut labels = StringMap::empty();
    labels.insert(new_strlit("app").to_string(), zk.name().unwrap());
    configmap.set_labels(labels);

    let mut data = StringMap::empty();
    data.insert(new_strlit("zoo.cfg").to_string(), make_zk_config());
    data.insert(new_strlit("log4j.properties").to_string(), make_log4j_config());
    data.insert(new_strlit("log4j-quiet.properties").to_string(), make_log4j_quiet_config());
    data.insert(new_strlit("env.sh").to_string(), make_env_config(zk));

    configmap.set_data(data);

    configmap
}

fn make_zk_config() -> (s: String)
    ensures
        s@ == zk_spec::make_zk_config(),
{
    new_strlit(
        "4lw.commands.whitelist=cons, envi, conf, crst, srvr, stat, mntr, ruok\n\
        dataDir=/data\n\
        standaloneEnabled=false\n\
        reconfigEnabled=true\n\
        skipACL=yes\n\
        metricsProvider.className=org.apache.zookeeper.metrics.prometheus.PrometheusMetricsProvider\n\
        metricsProvider.httpPort=7000\n\
        metricsProvider.exportJvmInfo=true\n\
        initLimit=10\n\
        syncLimit=2\n\
        tickTime=2000\n\
        globalOutstandingLimit=1000\n\
        preAllocSize=65536\n\
        snapCount=10000\n\
        commitLogCount=500\n\
        snapSizeLimitInKb=4194304\n\
        maxCnxns=0\n\
        maxClientCnxns=60\n\
        minSessionTimeout=4000\n\
        maxSessionTimeout=40000\n\
        autopurge.snapRetainCount=3\n\
        autopurge.purgeInterval=1\n\
        quorumListenOnAllIPs=false\n\
        admin.serverPort=8080\n\
        dynamicConfigFile=/data/zoo.cfg.dynamic\n"
    ).to_string()
}

fn make_log4j_config() -> (s: String)
    ensures
        s@ == zk_spec::make_log4j_config(),
{
    new_strlit(
        "zookeeper.root.logger=CONSOLE\n\
        zookeeper.console.threshold=INFO\n\
        log4j.rootLogger=${zookeeper.root.logger}\n\
        log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n\
        log4j.appender.CONSOLE.Threshold=${zookeeper.console.threshold}\n\
        log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n\
        log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    ).to_string()
}

fn make_log4j_quiet_config() -> (s: String)
    ensures
        s@ == zk_spec::make_log4j_quiet_config(),
{
    new_strlit(
        "log4j.rootLogger=ERROR, CONSOLE\n\
        log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n\
        log4j.appender.CONSOLE.Threshold=ERROR\n\
        log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n\
        log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    ).to_string()
}

fn make_env_config(zk: &ZookeeperCluster) -> (s: String)
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
    ensures
        s@ == zk_spec::make_env_config(zk@),
{
    let name = zk.name().unwrap();
    let namespace = zk.namespace().unwrap();

    new_strlit(
        "#!/usr/bin/env bash\n\n\
        DOMAIN=").to_string().concat(name.as_str()).concat(new_strlit("-headless.")).concat(namespace.as_str())
            .concat(new_strlit(".svc.cluster.local\n\
        QUORUM_PORT=2888\n\
        LEADER_PORT=3888\n\
        CLIENT_HOST=")).concat(name.as_str()).concat(new_strlit("-client\n\
        CLIENT_PORT=2181\n\
        ADMIN_SERVER_HOST=")).concat(name.as_str()).concat(new_strlit("-admin-server\n\
        ADMIN_SERVER_PORT=8080\n\
        CLUSTER_NAME=")).concat(name.as_str()).concat(new_strlit("\n\
        CLUSTER_SIZE=")).concat(i32_to_string(zk.replica()).as_str()).concat(new_strlit("\n"))
}

fn make_statefulset(zk: &ZookeeperCluster) -> (statefulset: StatefulSet)
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
{
    let mut statefulset = StatefulSet::default();
    statefulset.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(zk.name().unwrap());
        metadata.set_namespace(zk.namespace().unwrap());
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), zk.name().unwrap());
            labels
        });
        metadata
    });
    statefulset.set_spec({
        let mut statefulset_spec = StatefulSetSpec::default();
        statefulset_spec.set_replicas(zk.replica());
        statefulset_spec.set_service_name(zk.name().unwrap().concat(new_strlit("-headless")));
        statefulset_spec.set_selector({
            let mut selector = LabelSelector::default();
            selector.set_match_labels({
                let mut match_labels = StringMap::empty();
                match_labels.insert(new_strlit("app").to_string(), zk.name().unwrap());
                match_labels
            });
            selector
        });
        statefulset_spec.set_template({
            let mut pod_template_spec = PodTemplateSpec::default();
            pod_template_spec.set_metadata({
                let mut metadata = ObjectMeta::default();
                metadata.set_generate_name(zk.name().unwrap());
                metadata.set_labels({
                    let mut labels = StringMap::empty();
                    labels.insert(new_strlit("app").to_string(), zk.name().unwrap());
                    labels.insert(new_strlit("kind").to_string(), new_strlit("ZookeeperMember").to_string());
                    labels
                });
                metadata
            });
            pod_template_spec.set_spec(make_zk_pod_spec(zk));
            pod_template_spec
        });
        statefulset_spec.set_volume_claim_templates({
            let mut volume_claim_templates = Vec::empty();
            volume_claim_templates.push({
                let mut pvc = PersistentVolumeClaim::default();
                pvc.set_metadata({
                    let mut metadata = ObjectMeta::default();
                    metadata.set_name(new_strlit("data").to_string());
                    metadata.set_labels({
                        let mut labels = StringMap::empty();
                        labels.insert(new_strlit("app").to_string(), zk.name().unwrap());
                        labels
                    });
                    metadata
                });
                pvc.set_spec({
                    let mut pvc_spec = PersistentVolumeClaimSpec::default();
                    pvc_spec.set_access_modes({
                        let mut access_modes = Vec::empty();
                        access_modes.push(new_strlit("ReadWriteOnce").to_string());
                        access_modes
                    });
                    pvc_spec.set_resources(make_resource_requirements());
                    pvc_spec
                });
                pvc
            });
            volume_claim_templates
        });
        statefulset_spec
    });
    statefulset
}

fn make_zk_pod_spec(zk: &ZookeeperCluster) -> (pod_spec: PodSpec)
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
{
    let mut pod_spec = PodSpec::default();

    pod_spec.set_containers({
        let mut zk_container = Container::default();
        zk_container.set_name(new_strlit("zookeeper").to_string());
        zk_container.set_image(new_strlit("pravega/zookeeper:0.2.14").to_string());
        zk_container.set_command({
            let mut command = Vec::empty();
            command.push(new_strlit("/usr/local/bin/zookeeperStart.sh").to_string());
            command
        });
        zk_container.set_image_pull_policy(new_strlit("Always").to_string());
        zk_container.set_volume_mounts({
            let mut volume_mounts = Vec::empty();
            volume_mounts.push({
                let mut data_volume_mount = VolumeMount::default();
                data_volume_mount.set_name(new_strlit("data").to_string());
                data_volume_mount.set_mount_path(new_strlit("/data").to_string());
                data_volume_mount
            });
            volume_mounts.push({
                let mut conf_volume_mount = VolumeMount::default();
                conf_volume_mount.set_name(new_strlit("conf").to_string());
                conf_volume_mount.set_mount_path(new_strlit("/conf").to_string());
                conf_volume_mount
            });
            volume_mounts
        });
        zk_container.set_ports({
            let mut ports = Vec::empty();
            ports.push(ContainerPort::new_with(new_strlit("client").to_string(), 2181));
            ports.push(ContainerPort::new_with(new_strlit("quorum").to_string(), 2888));
            ports.push(ContainerPort::new_with(new_strlit("leader-election").to_string(), 3888));
            ports.push(ContainerPort::new_with(new_strlit("metrics").to_string(), 7000));
            ports.push(ContainerPort::new_with(new_strlit("admin-server").to_string(), 8080));
            ports
        });
        zk_container.set_readiness_probe(make_readiness_probe());
        zk_container.set_liveness_probe(make_liveness_probe());

        let mut containers = Vec::empty();
        containers.push(zk_container);

        containers
    });
    pod_spec.set_volumes({
        let mut volumes = Vec::empty();
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("conf").to_string());
            volume.set_config_map({
                let mut config_map = ConfigMapVolumeSource::default();
                config_map.set_name(zk.name().unwrap().concat(new_strlit("-configmap")));
                config_map
            });
            volume
        });
        volumes
    });

    pod_spec
}

#[verifier(external_body)]
fn make_readiness_probe() -> Probe
{
    Probe::from_kube(
        k8s_openapi::api::core::v1::Probe {
            exec: std::option::Option::Some(k8s_openapi::api::core::v1::ExecAction {
                command: std::option::Option::Some(vec!["zookeeperReady.sh".to_string()]),
            }),
            failure_threshold: std::option::Option::Some(3),
            initial_delay_seconds: std::option::Option::Some(10),
            period_seconds: std::option::Option::Some(10),
            success_threshold: std::option::Option::Some(1),
            timeout_seconds: std::option::Option::Some(10),
            ..k8s_openapi::api::core::v1::Probe::default()
        }
    )
}

#[verifier(external_body)]
fn make_liveness_probe() -> Probe
{
    Probe::from_kube(
        k8s_openapi::api::core::v1::Probe {
            exec: std::option::Option::Some(k8s_openapi::api::core::v1::ExecAction {
                command: std::option::Option::Some(vec!["zookeeperLive.sh".to_string()]),
            }),
            failure_threshold: std::option::Option::Some(3),
            initial_delay_seconds: std::option::Option::Some(10),
            period_seconds: std::option::Option::Some(10),
            success_threshold: std::option::Option::Some(1),
            timeout_seconds: std::option::Option::Some(10),
            ..k8s_openapi::api::core::v1::Probe::default()
        }
    )
}

#[verifier(external_body)]
fn make_resource_requirements() -> ResourceRequirements
{
    ResourceRequirements::from_kube(
        k8s_openapi::api::core::v1::ResourceRequirements {
            requests: std::option::Option::Some(std::collections::BTreeMap::from([(
                "storage".to_string(),
                k8s_openapi::apimachinery::pkg::api::resource::Quantity("20Gi".to_string()),
            )])),
            ..k8s_openapi::api::core::v1::ResourceRequirements::default()
        }
    )
}

}
