// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use crate::zookeeper_controller::exec::resource::{common::*, stateful_set::StatefulSetBuilder};
use crate::zookeeper_controller::model::resource as model_resource;
use crate::zookeeper_controller::trusted::{
    config_map, exec_types::*, spec_types::ZookeeperClusterView, step::*,
};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ConfigMapBuilder {}

impl ResourceBuilder<ZookeeperCluster, ZookeeperReconcileState, model_resource::ConfigMapBuilder> for ConfigMapBuilder {
    open spec fn requirements(zk: ZookeeperClusterView) -> bool { zk.well_formed() }

    fn get_request(zk: &ZookeeperCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: ConfigMap::api_resource(),
            name: make_config_map_name(zk),
            namespace: zk.metadata().namespace().unwrap(),
        }
    }

    fn make(zk: &ZookeeperCluster, state: &ZookeeperReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_config_map(zk).marshal())
    }

    fn update(zk: &ZookeeperCluster, state: &ZookeeperReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let cm = ConfigMap::unmarshal(obj);
        if cm.is_ok() {
            return Ok(update_config_map(zk, &cm.unwrap()).marshal());
        }
        return Err(());
    }

    fn state_after_create(zk: &ZookeeperCluster, obj: DynamicObject, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<KubeAPIRequest>), ()>) {
        let cm = ConfigMap::unmarshal(obj);
        if cm.is_ok() && cm.as_ref().unwrap().metadata().resource_version().is_some() {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterExistsStatefulSet,
                latest_config_map_rv_opt: Some(cm.unwrap().metadata().resource_version().unwrap()),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(StatefulSetBuilder::get_request(zk));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    fn state_after_update(zk: &ZookeeperCluster, obj: DynamicObject, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<KubeAPIRequest>), ()>) {
        let cm = ConfigMap::unmarshal(obj);
        if cm.is_ok() && cm.as_ref().unwrap().metadata().resource_version().is_some() {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterExistsStatefulSet,
                latest_config_map_rv_opt: Some(cm.unwrap().metadata().resource_version().unwrap()),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(StatefulSetBuilder::get_request(zk));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub fn make_config_map_name(zk: &ZookeeperCluster) -> (name: String)
    requires zk@.well_formed(),
    ensures name@ == model_resource::make_config_map_name(zk@),
{
    zk.metadata().name().unwrap().concat(new_strlit("-configmap"))
}

pub fn update_config_map(zk: &ZookeeperCluster, found_config_map: &ConfigMap) -> (config_map: ConfigMap)
    requires zk@.well_formed(),
    ensures config_map@ == model_resource::update_config_map(zk@, found_config_map@),
{
    let mut config_map = found_config_map.clone();
    let made_config_map = make_config_map(zk);
    config_map.set_metadata({
        let mut metadata = found_config_map.metadata();
        metadata.set_owner_references(make_owner_references(zk));
        metadata.unset_finalizers();
        metadata.set_labels(made_config_map.metadata().labels().unwrap());
        metadata.set_annotations(made_config_map.metadata().annotations().unwrap());
        metadata
    });
    config_map.set_data(made_config_map.data().unwrap());
    config_map
}

/// The ConfigMap stores the configuration data of zookeeper servers
pub fn make_config_map(zk: &ZookeeperCluster) -> (config_map: ConfigMap)
    requires zk@.well_formed(),
    ensures config_map@ == model_resource::make_config_map(zk@),
{
    let mut config_map = ConfigMap::default();

    config_map.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_config_map_name(zk));
        metadata.set_labels(make_labels(zk));
        metadata.set_annotations(zk.spec().annotations());
        metadata.set_owner_references(make_owner_references(zk));
        metadata
    });
    config_map.set_data({
        let mut data = StringMap::empty();
        data.insert(new_strlit("zoo.cfg").to_string(), make_zk_config(zk));
        data.insert(new_strlit("log4j.properties").to_string(), make_log4j_config());
        data.insert(new_strlit("log4j-quiet.properties").to_string(), make_log4j_quiet_config());
        data.insert(new_strlit("env.sh").to_string(), make_env_config(zk));
        data
    });

    config_map
}

pub fn make_zk_config(zk: &ZookeeperCluster) -> (s: String)
    ensures s@ == config_map::make_zk_config(zk@),
{
    new_strlit(
        "4lw.commands.whitelist=cons, envi, conf, crst, srvr, stat, mntr, ruok\n\
        dataDir=/data\n\
        standaloneEnabled=false\n\
        reconfigEnabled=true\n\
        skipACL=yes\n\
        metricsProvider.className=org.apache.zookeeper.metrics.prometheus.PrometheusMetricsProvider\n\
        metricsProvider.httpPort=").to_string().concat(i32_to_string(zk.spec().ports().metrics()).as_str()).concat(new_strlit("\n\
        metricsProvider.exportJvmInfo=true\n\
        initLimit=")).concat(i32_to_string(zk.spec().conf().init_limit()).as_str()).concat(new_strlit("\n\
        syncLimit=")).concat(i32_to_string(zk.spec().conf().sync_limit()).as_str()).concat(new_strlit("\n\
        tickTime=")).concat(i32_to_string(zk.spec().conf().tick_time()).as_str()).concat(new_strlit("\n\
        globalOutstandingLimit=")).concat(i32_to_string(zk.spec().conf().global_outstanding_limit()).as_str()).concat(new_strlit("\n\
        preAllocSize=")).concat(i32_to_string(zk.spec().conf().pre_alloc_size()).as_str()).concat(new_strlit("\n\
        snapCount=")).concat(i32_to_string(zk.spec().conf().snap_count()).as_str()).concat(new_strlit("\n\
        commitLogCount=")).concat(i32_to_string(zk.spec().conf().commit_log_count()).as_str()).concat(new_strlit("\n\
        snapSizeLimitInKb=")).concat(i32_to_string(zk.spec().conf().snap_size_limit_in_kb()).as_str()).concat(new_strlit("\n\
        maxCnxns=")).concat(i32_to_string(zk.spec().conf().max_cnxns()).as_str()).concat(new_strlit("\n\
        maxClientCnxns=")).concat(i32_to_string(zk.spec().conf().max_client_cnxns()).as_str()).concat(new_strlit("\n\
        minSessionTimeout=")).concat(i32_to_string(zk.spec().conf().min_session_timeout()).as_str()).concat(new_strlit("\n\
        maxSessionTimeout=")).concat(i32_to_string(zk.spec().conf().max_session_timeout()).as_str()).concat(new_strlit("\n\
        autopurge.snapRetainCount=")).concat(i32_to_string(zk.spec().conf().auto_purge_snap_retain_count()).as_str()).concat(new_strlit("\n\
        autopurge.purgeInterval=")).concat(i32_to_string(zk.spec().conf().auto_purge_purge_interval()).as_str()).concat(new_strlit("\n\
        quorumListenOnAllIPs=")).concat(bool_to_string(zk.spec().conf().quorum_listen_on_all_ips()).as_str()).concat(new_strlit("\n\
        admin.serverPort=")).concat(i32_to_string(zk.spec().ports().admin_server()).as_str()).concat(new_strlit("\n\
        dynamicConfigFile=/data/zoo.cfg.dynamic\n"
    ))
}

pub fn make_log4j_config() -> (s: String)
    ensures s@ == model_resource::make_log4j_config(),
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

pub fn make_log4j_quiet_config() -> (s: String)
    ensures s@ == model_resource::make_log4j_quiet_config(),
{
    new_strlit(
        "log4j.rootLogger=ERROR, CONSOLE\n\
        log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n\
        log4j.appender.CONSOLE.Threshold=ERROR\n\
        log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n\
        log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    ).to_string()
}

pub fn make_env_config(zk: &ZookeeperCluster) -> (s: String)
    requires zk@.well_formed(),
    ensures s@ == model_resource::make_env_config(zk@),
{
    let name = zk.metadata().name().unwrap();
    let namespace = zk.metadata().namespace().unwrap();
    let client_port = i32_to_string(zk.spec().ports().client());
    let quorum_port = i32_to_string(zk.spec().ports().quorum());
    let leader_election_port = i32_to_string(zk.spec().ports().leader_election());
    let admin_port = i32_to_string(zk.spec().ports().admin_server());

    new_strlit(
        "#!/usr/bin/env bash\n\n\
        DOMAIN=").to_string().concat(name.as_str()).concat(new_strlit("-headless.")).concat(namespace.as_str())
            .concat(new_strlit(".svc.cluster.local\n\
        QUORUM_PORT=")).concat(quorum_port.as_str()).concat(new_strlit("\n\
        LEADER_PORT=")).concat(leader_election_port.as_str()).concat(new_strlit("\n\
        CLIENT_HOST=")).concat(name.as_str()).concat(new_strlit("-client\n\
        CLIENT_PORT=")).concat(client_port.as_str()).concat(new_strlit("\n\
        ADMIN_SERVER_HOST=")).concat(name.as_str()).concat(new_strlit("-admin-server\n\
        ADMIN_SERVER_PORT=")).concat(admin_port.as_str()).concat(new_strlit("\n\
        CLUSTER_NAME=")).concat(name.as_str()).concat(new_strlit("\n"))
}

}
