// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_examples::zookeeper_controller::common::*;
use crate::controller_examples::zookeeper_controller::spec::zookeepercluster::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, object_meta::*, resource::*, service::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_const::*;
use crate::pervasive_ext::string_view::*;
use crate::reconciler::spec::*;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ZookeeperReconcileState {
    pub reconcile_step: ZookeeperReconcileStep,

    pub zk: Option<ZookeeperClusterView>,
}

pub open spec fn reconcile_init_state() -> ZookeeperReconcileState {
    ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Init,
        zk: Option::None,
    }
}

pub open spec fn reconcile_done(state: ZookeeperReconcileState) -> bool {
    match state.reconcile_step {
        ZookeeperReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: ZookeeperReconcileState) -> bool {
    match state.reconcile_step {
        ZookeeperReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(zk_ref: ObjectRef, resp_o: Option<APIResponse>, state: ZookeeperReconcileState) -> (ZookeeperReconcileState, Option<APIRequest>)
    recommends
        zk_ref.kind.is_CustomResourceKind(),
{
    let step = state.reconcile_step;
    match step {
        ZookeeperReconcileStep::Init => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterGetZK,
                ..state
            };
            let req_o = Option::Some(APIRequest::GetRequest(GetRequest{key: zk_ref}));
            (state_prime, req_o)
        },
        ZookeeperReconcileStep::AfterGetZK => {
            let resp = resp_o.get_Some_0();
            let zk = ZookeeperClusterView::from_dynamic_object(resp.get_GetResponse_0().res.get_Ok_0());
            if !resp_o.is_Some()
                || !(resp.is_GetResponse() && resp.get_GetResponse_0().res.is_Ok())
                || !(zk.metadata.name.is_Some() && zk.metadata.namespace.is_Some()) {
                reconcile_error_result(state)
            } else {
                let headless_service = make_headless_service(zk);
                let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                    obj: headless_service.to_dynamic_object(),
                }));
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterCreateHeadlessService,
                    zk: Option::Some(zk),
                    ..state
                };
                (state_prime, req_o)
            }
        },
        ZookeeperReconcileStep::AfterCreateHeadlessService => {
            let zk = state.zk.get_Some_0();
            if !state.zk.is_Some() || !(zk.metadata.name.is_Some() && zk.metadata.namespace.is_Some()) {
                reconcile_error_result(state)
            } else {
                let client_service = make_client_service(zk);
                let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                    obj: client_service.to_dynamic_object(),
                }));
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterCreateClientService,
                    ..state
                };
                (state_prime, req_o)
            }
        },
        ZookeeperReconcileStep::AfterCreateClientService => {
            let zk = state.zk.get_Some_0();
            if !state.zk.is_Some() || !(zk.metadata.name.is_Some() && zk.metadata.namespace.is_Some()) {
                reconcile_error_result(state)
            } else {
                let admin_server_service = make_admin_server_service(zk);
                let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                    obj: admin_server_service.to_dynamic_object(),
                }));
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterCreateAdminServerService,
                    ..state
                };
                (state_prime, req_o)
            }
        },
        ZookeeperReconcileStep::AfterCreateAdminServerService => {
            let zk = state.zk.get_Some_0();
            if !state.zk.is_Some() || !(zk.metadata.name.is_Some() && zk.metadata.namespace.is_Some()) {
                reconcile_error_result(state)
            } else {
                let configmap = make_configmap(zk);
                let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                    obj: configmap.to_dynamic_object(),
                }));
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Done,
                    ..state
                };
                (state_prime, req_o)
            }
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

pub open spec fn reconcile_error_result(state: ZookeeperReconcileState) -> (ZookeeperReconcileState, Option<APIRequest>) {
    let state_prime = ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Error,
        ..state
    };
    let req_o = Option::None;
    (state_prime, req_o)
}

pub open spec fn make_headless_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let ports = Seq::empty()
        .push(ServicePortView::default().set_name(new_strlit("tcp-client")@).set_port(2181))
        .push(ServicePortView::default().set_name(new_strlit("tcp-quorum")@).set_port(2888))
        .push(ServicePortView::default().set_name(new_strlit("tcp-leader-election")@).set_port(3888))
        .push(ServicePortView::default().set_name(new_strlit("tcp-metrics")@).set_port(7000))
        .push(ServicePortView::default().set_name(new_strlit("tcp-admin-server")@).set_port(8080));

    make_service(zk, zk.metadata.name.get_Some_0() + new_strlit("-headless")@, ports, false)
}

pub open spec fn make_client_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let ports = Seq::empty().push(ServicePortView::default().set_name(new_strlit("tcp-client")@).set_port(2181));

    make_service(zk, zk.metadata.name.get_Some_0() + new_strlit("-client")@, ports, true)
}

pub open spec fn make_admin_server_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let ports = Seq::empty().push(ServicePortView::default().set_name(new_strlit("tcp-admin-server")@).set_port(8080));

    make_service(zk, zk.metadata.name.get_Some_0() + new_strlit("-admin-server")@, ports, true)
}

pub open spec fn make_service(
    zk: ZookeeperClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool
) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let labels = Map::empty().insert(new_strlit("app")@, zk.metadata.name.get_Some_0());
    let metadata = ObjectMetaView::default()
        .set_name(name)
        .set_namespace(zk.metadata.namespace.get_Some_0())
        .set_labels(labels);

    let selector = Map::empty().insert(new_strlit("app")@, zk.metadata.name.get_Some_0());
    let service_spec = if !cluster_ip {
        ServiceSpecView::default().set_cluster_ip(new_strlit("None")@).set_ports(ports).set_selector(selector)
    } else {
        ServiceSpecView::default().set_ports(ports).set_selector(selector)
    };

    ServiceView::default().set_metadata(metadata).set_spec(service_spec)
}

pub open spec fn make_configmap(zk: ZookeeperClusterView) -> ConfigMapView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let labels = Map::empty().insert(new_strlit("app")@, zk.metadata.name.get_Some_0());
    let data = Map::empty()
        .insert(new_strlit("zoo.cfg")@, make_zk_config())
        .insert(new_strlit("log4j.properties")@, make_log4j_config())
        .insert(new_strlit("log4j-quiet.properties")@, make_log4j_quiet_config())
        .insert(new_strlit("env.sh")@, make_env_config(zk));

    ConfigMapView::default()
        .set_name(zk.metadata.name.get_Some_0() + new_strlit("-configmap")@)
        .set_namespace(zk.metadata.namespace.get_Some_0())
        .set_labels(labels)
        .set_data(data)
}

pub open spec fn make_zk_config() -> StringView {
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
    )@
}

pub open spec fn make_log4j_config() -> StringView {
    new_strlit(
        "zookeeper.root.logger=CONSOLE\n\
        zookeeper.console.threshold=INFO\n\
        log4j.rootLogger=${zookeeper.root.logger}\n\
        log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n\
        log4j.appender.CONSOLE.Threshold=${zookeeper.console.threshold}\n\
        log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n\
        log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    )@
}

pub open spec fn make_log4j_quiet_config() -> StringView {
    new_strlit(
        "log4j.rootLogger=ERROR, CONSOLE\n\
        log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n\
        log4j.appender.CONSOLE.Threshold=ERROR\n\
        log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n\
        log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    )@
}

pub open spec fn make_env_config(zk: ZookeeperClusterView) -> StringView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let name = zk.metadata.name.get_Some_0();
    let namespace = zk.metadata.namespace.get_Some_0();

    new_strlit(
        "#!/usr/bin/env bash\n\n\
        DOMAIN=")@ + name + new_strlit("-headless.")@ + namespace + new_strlit(".svc.cluster.local\n\
        QUORUM_PORT=2888\n\
        LEADER_PORT=3888\n\
        CLIENT_HOST=")@ + name + new_strlit("-client\n\
        CLIENT_PORT=2181\n\
        ADMIN_SERVER_HOST=")@ + name + new_strlit("-admin-server\n\
        ADMIN_SERVER_PORT=8080\n\
        CLUSTER_NAME=")@ + name + new_strlit("\n\
        CLUSTER_SIZE=")@ + int_to_string_view(zk.spec.replica) + new_strlit("\n")@
}

}
