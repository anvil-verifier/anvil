// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::vstd_ext::string_view::*;
use crate::zookeeper_controller::trusted::spec_types::*;
use vstd::{prelude::*, string::*};

verus! {

pub open spec fn make_zk_config(zk: ZookeeperClusterView) -> StringView {
    "4lw.commands.whitelist=cons, envi, conf, crst, srvr, stat, mntr, ruok\n\
    dataDir=/data\n\
    standaloneEnabled=false\n\
    reconfigEnabled=true\n\
    skipACL=yes\n\
    metricsProvider.className=org.apache.zookeeper.metrics.prometheus.PrometheusMetricsProvider\n\
    metricsProvider.httpPort="@ + int_to_string_view(zk.spec.ports.metrics) + "\n\
    metricsProvider.exportJvmInfo=true\n\
    initLimit="@ + int_to_string_view(zk.spec.conf.init_limit) + "\n\
    syncLimit="@ + int_to_string_view(zk.spec.conf.sync_limit) + "\n\
    tickTime="@ + int_to_string_view(zk.spec.conf.tick_time) + "\n\
    globalOutstandingLimit="@ + int_to_string_view(zk.spec.conf.global_outstanding_limit) + "\n\
    preAllocSize="@ + int_to_string_view(zk.spec.conf.pre_alloc_size) + "\n\
    snapCount="@ + int_to_string_view(zk.spec.conf.snap_count) + "\n\
    commitLogCount="@ + int_to_string_view(zk.spec.conf.commit_log_count) + "\n\
    snapSizeLimitInKb="@ + int_to_string_view(zk.spec.conf.snap_size_limit_in_kb) + "\n\
    maxCnxns="@ + int_to_string_view(zk.spec.conf.max_cnxns) + "\n\
    maxClientCnxns="@ + int_to_string_view(zk.spec.conf.max_client_cnxns) + "\n\
    minSessionTimeout="@ + int_to_string_view(zk.spec.conf.min_session_timeout) + "\n\
    maxSessionTimeout="@ + int_to_string_view(zk.spec.conf.max_session_timeout) + "\n\
    autopurge.snapRetainCount="@ + int_to_string_view(zk.spec.conf.auto_purge_snap_retain_count) + "\n\
    autopurge.purgeInterval="@ + int_to_string_view(zk.spec.conf.auto_purge_purge_interval) + "\n\
    quorumListenOnAllIPs="@ + bool_to_string_view(zk.spec.conf.quorum_listen_on_all_ips) + "\n\
    admin.serverPort="@ + int_to_string_view(zk.spec.ports.admin_server) + "\n\
    dynamicConfigFile=/data/zoo.cfg.dynamic\n"@
}

}
