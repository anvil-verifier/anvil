// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_examples::zookeeper_controller::spec::reconciler as zk_spec;
use crate::controller_examples::zookeeper_controller::spec::zookeepercluster::*;
use crate::kubernetes_api_objects::{api_method::*, common::*, config_map::*, service::*};
use crate::pervasive_ext::string_map::StringMap;
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

#[is_variant]
pub enum ZookeeperReconcileStep {
    Init,
    AfterGetZK,
    AfterCreateHeadlessService,
    AfterCreateClientService,
    AfterCreateAdminServerService,
    Done,
    Error,
}

impl ZookeeperReconcileStep {
    pub fn clone(&self) -> (res: ZookeeperReconcileStep)
        ensures res == self
    {
        match self {
            ZookeeperReconcileStep::Init => ZookeeperReconcileStep::Init,
            ZookeeperReconcileStep::AfterGetZK => ZookeeperReconcileStep::AfterGetZK,
            ZookeeperReconcileStep::AfterCreateHeadlessService => ZookeeperReconcileStep::AfterCreateHeadlessService,
            ZookeeperReconcileStep::AfterCreateClientService => ZookeeperReconcileStep::AfterCreateClientService,
            ZookeeperReconcileStep::AfterCreateAdminServerService => ZookeeperReconcileStep::AfterCreateAdminServerService,
            ZookeeperReconcileStep::Done => ZookeeperReconcileStep::Done,
            ZookeeperReconcileStep::Error => ZookeeperReconcileStep::Error,
        }
    }
}

pub struct ZookeeperReconciler {}

#[verifier(external)]
impl Reconciler<ZookeeperReconcileState> for ZookeeperReconciler {
    fn reconcile_init_state(&self) -> ZookeeperReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, cr_key: &KubeObjectRef, resp_o: Option<KubeAPIResponse>, state: ZookeeperReconcileState) -> (ZookeeperReconcileState, Option<KubeAPIRequest>) {
        reconcile_core(cr_key, resp_o, state)
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

pub fn reconcile_init_state() -> ZookeeperReconcileState {
    ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Init,
        zk: Option::None,
    }
}

pub fn reconcile_done(state: &ZookeeperReconcileState) -> (res: bool) {
    match state.reconcile_step {
        ZookeeperReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &ZookeeperReconcileState) -> (res: bool) {
    match state.reconcile_step {
        ZookeeperReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(cr_key: &KubeObjectRef, resp_o: Option<KubeAPIResponse>, state: ZookeeperReconcileState) -> (res: (ZookeeperReconcileState, Option<KubeAPIRequest>)) {
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
                    name: cr_key.name.clone(),
                    namespace: cr_key.namespace.clone(),
                }
            ));
            (state_prime, req_o)
        },
        ZookeeperReconcileStep::AfterGetZK => {
            if resp_o.is_some() {
                let resp = resp_o.unwrap();
                if resp.is_get_response() && resp.as_get_response_ref().res.is_ok() {
                    let zk = ZookeeperCluster::from_dynamic_object(resp.into_get_response().res.unwrap());
                    if zk.name().is_some() && zk.namespace().is_some() {
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
                        return (state_prime, req_o)
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            let req_o = Option::None;
            return (state_prime, req_o)
        },
        ZookeeperReconcileStep::AfterCreateHeadlessService => {
            if state.zk.is_some() {
                let zk = state.zk.as_ref().unwrap();
                if zk.name().is_some() && zk.namespace().is_some() {
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
                    return (state_prime, req_o)
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            let req_o = Option::None;
            return (state_prime, req_o)
        },
        ZookeeperReconcileStep::AfterCreateClientService => {
            if state.zk.is_some() {
                let zk = state.zk.as_ref().unwrap();
                if zk.name().is_some() && zk.namespace().is_some() {
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
                    return (state_prime, req_o)
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            let req_o = Option::None;
            return (state_prime, req_o)
        },
        ZookeeperReconcileStep::AfterCreateAdminServerService => {
            if state.zk.is_some() {
                let zk = state.zk.as_ref().unwrap();
                if zk.name().is_some() && zk.namespace().is_some() {
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
                    return (state_prime, req_o)
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            let req_o = Option::None;
            return (state_prime, req_o)
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
    let mut service = Service::default();
    service.set_name(name);
    service.set_namespace(zk.namespace().unwrap());

    let mut labels = StringMap::empty();
    labels.insert(new_strlit("app").to_string(), zk.name().unwrap());
    service.set_labels(labels);

    let mut service_spec = ServiceSpec::default();
    if !cluster_ip {
        service_spec.set_cluster_ip(new_strlit("None").to_string());
    }
    service_spec.set_ports(ports);

    let mut selector = StringMap::empty();
    selector.insert(new_strlit("app").to_string(), zk.name().unwrap());
    service_spec.set_selector(selector);

    service.set_spec(service_spec);

    service
}

fn make_configmap(zk: &ZookeeperCluster) -> ConfigMap
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
{
    let mut configmap = ConfigMap::default();
    configmap.set_name(zk.name().unwrap().concat(new_strlit("-configmap")));
    configmap.set_namespace(zk.namespace().unwrap());

    let mut data = StringMap::empty();
    data.insert(new_strlit("zoo.cfg").to_string(), make_zk_config());
    data.insert(new_strlit("log4j.properties").to_string(), make_log4j_config());
    data.insert(new_strlit("log4j-quiet.properties").to_string(), make_log4j_quiet_config());
    data.insert(new_strlit("env.sh").to_string(), make_env_config(zk));

    configmap.set_data(data);

    configmap
}

fn make_zk_config() -> String
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

fn make_log4j_config() -> String
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

fn make_log4j_quiet_config() -> String
{
    new_strlit(
        "log4j.rootLogger=ERROR, CONSOLE\n\
        log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n\
        log4j.appender.CONSOLE.Threshold=ERROR\n\
        log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n\
        log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    ).to_string()
}

fn make_env_config(zk: &ZookeeperCluster) -> String
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
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
        CLUSTER_SIZE=")).concat(int_to_string(zk.replica()).as_str()).concat(new_strlit("\n"))
}

#[verifier(external_body)]
fn int_to_string(i: i32) -> String {
    String::from_rust_string(i.to_string())
}

}
