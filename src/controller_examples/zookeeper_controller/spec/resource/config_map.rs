// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ConfigMapBuilder {}

impl ResourceBuilder<ZookeeperClusterView, ZookeeperReconcileState> for ConfigMapBuilder {
    open spec fn get_request(rabbitmq: ZookeeperClusterView) -> GetRequest {
        GetRequest { key: make_config_map_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: ZookeeperClusterView, state: ZookeeperReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_config_map(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: ZookeeperClusterView, state: ZookeeperReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let cm = ConfigMapView::unmarshal(obj);
        if cm.is_ok() {
            Ok(update_config_map(rabbitmq, cm.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create_or_update(obj: DynamicObjectView, state: ZookeeperReconcileState) -> (res: Result<ZookeeperReconcileState, ()>) {
        let cm = ConfigMapView::unmarshal(obj);
        if cm.is_ok() && cm.get_Ok_0().metadata.resource_version.is_Some() {
            Ok(ZookeeperReconcileState {
                latest_config_map_rv_opt: Some(int_to_string_view(cm.get_Ok_0().metadata.resource_version.get_Some_0())),
                ..state
            })
        } else {
            Err(())
        }
    }

    open spec fn resource_state_matches(rabbitmq: ZookeeperClusterView, resources: StoredState) -> bool {
        let key = make_config_map_key(rabbitmq);
        let obj = resources[key];
        &&& resources.contains_key(key)
        &&& ConfigMapView::unmarshal(obj).is_Ok()
        &&& ConfigMapView::unmarshal(obj).get_Ok_0().data == make_config_map(rabbitmq).data
        &&& obj.spec == ConfigMapView::marshal_spec((make_config_map(rabbitmq).data, ()))
        &&& obj.metadata.labels == make_config_map(rabbitmq).metadata.labels
        &&& obj.metadata.annotations == make_config_map(rabbitmq).metadata.annotations
    }

    open spec fn unchangeable(object: DynamicObjectView, rabbitmq: ZookeeperClusterView) -> bool {
        true
    }
}

pub open spec fn make_config_map_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: ConfigMapView::kind(),
        name: make_config_map_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn make_config_map_name(zk_name: StringView) -> StringView {
    zk_name + new_strlit("-configmap")@
}

pub open spec fn make_config_map(zk: ZookeeperClusterView) -> ConfigMapView
    recommends
        zk.well_formed(),
{
    ConfigMapView {
        metadata: ObjectMetaView {
            name: Some(make_config_map_name(zk.metadata.name.get_Some_0())),
            owner_references: Some(make_owner_references(zk)),
            labels: Some(make_labels(zk)),
            annotations: Some(zk.spec.annotations),
            ..ConfigMapView::default().metadata
        },
        data: Some(Map::empty()
            .insert(new_strlit("zoo.cfg")@, make_zk_config(zk))
            .insert(new_strlit("log4j.properties")@, make_log4j_config())
            .insert(new_strlit("log4j-quiet.properties")@, make_log4j_quiet_config())
            .insert(new_strlit("env.sh")@, make_env_config(zk))
        ),
        ..ConfigMapView::default()
    }
}

pub open spec fn update_config_map(zk: ZookeeperClusterView, found_config_map: ConfigMapView) -> ConfigMapView
    recommends
        zk.well_formed(),
{
    ConfigMapView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(zk)),
            finalizers: None,
            labels: make_config_map(zk).metadata.labels,
            annotations: make_config_map(zk).metadata.annotations,
            ..found_config_map.metadata
        },
        data: make_config_map(zk).data,
        ..found_config_map
    }
}

pub open spec fn make_zk_config(zk: ZookeeperClusterView) -> StringView {
    new_strlit(
        "4lw.commands.whitelist=cons, envi, conf, crst, srvr, stat, mntr, ruok\n\
        dataDir=/data\n\
        standaloneEnabled=false\n\
        reconfigEnabled=true\n\
        skipACL=yes\n\
        metricsProvider.className=org.apache.zookeeper.metrics.prometheus.PrometheusMetricsProvider\n\
        metricsProvider.httpPort=")@ + int_to_string_view(zk.spec.ports.metrics) + new_strlit("\n\
        metricsProvider.exportJvmInfo=true\n\
        initLimit=")@ + int_to_string_view(zk.spec.conf.init_limit) + new_strlit("\n\
        syncLimit=")@ + int_to_string_view(zk.spec.conf.sync_limit) + new_strlit("\n\
        tickTime=")@ + int_to_string_view(zk.spec.conf.tick_time) + new_strlit("\n\
        globalOutstandingLimit=")@ + int_to_string_view(zk.spec.conf.global_outstanding_limit) + new_strlit("\n\
        preAllocSize=")@ + int_to_string_view(zk.spec.conf.pre_alloc_size) + new_strlit("\n\
        snapCount=")@ + int_to_string_view(zk.spec.conf.snap_count) + new_strlit("\n\
        commitLogCount=")@ + int_to_string_view(zk.spec.conf.commit_log_count) + new_strlit("\n\
        snapSizeLimitInKb=")@ + int_to_string_view(zk.spec.conf.snap_size_limit_in_kb) + new_strlit("\n\
        maxCnxns=")@ + int_to_string_view(zk.spec.conf.max_cnxns) + new_strlit("\n\
        maxClientCnxns=")@ + int_to_string_view(zk.spec.conf.max_client_cnxns) + new_strlit("\n\
        minSessionTimeout=")@ + int_to_string_view(zk.spec.conf.min_session_timeout) + new_strlit("\n\
        maxSessionTimeout=")@ + int_to_string_view(zk.spec.conf.max_session_timeout) + new_strlit("\n\
        autopurge.snapRetainCount=")@ + int_to_string_view(zk.spec.conf.auto_purge_snap_retain_count) + new_strlit("\n\
        autopurge.purgeInterval=")@ + int_to_string_view(zk.spec.conf.auto_purge_purge_interval) + new_strlit("\n\
        quorumListenOnAllIPs=")@ + bool_to_string_view(zk.spec.conf.quorum_listen_on_all_ips) + new_strlit("\n\
        admin.serverPort=")@ + int_to_string_view(zk.spec.ports.admin_server) + new_strlit("\n\
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
        zk.well_formed(),
{
    let name = zk.metadata.name.get_Some_0();
    let namespace = zk.metadata.namespace.get_Some_0();
    let client_port = int_to_string_view(zk.spec.ports.client);
    let quorum_port = int_to_string_view(zk.spec.ports.quorum);
    let leader_election_port = int_to_string_view(zk.spec.ports.leader_election);
    let admin_server_port = int_to_string_view(zk.spec.ports.admin_server);

    new_strlit(
        "#!/usr/bin/env bash\n\n\
        DOMAIN=")@ + name + new_strlit("-headless.")@ + namespace + new_strlit(".svc.cluster.local\n\
        QUORUM_PORT=")@ + quorum_port + new_strlit("\n\
        LEADER_PORT=")@ + leader_election_port + new_strlit("\n\
        CLIENT_HOST=")@ + name + new_strlit("-client\n\
        CLIENT_PORT=")@ + client_port + new_strlit("\n\
        ADMIN_SERVER_HOST=")@ + name + new_strlit("-admin-server\n\
        ADMIN_SERVER_PORT=")@ + admin_server_port + new_strlit("\n\
        CLUSTER_NAME=")@ + name + new_strlit("\n")@
}

}