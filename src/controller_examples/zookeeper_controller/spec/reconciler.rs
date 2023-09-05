// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, container::*, error::*, label_selector::*,
    object_meta::*, persistent_volume_claim::*, pod::*, pod_template_spec::*, resource::*,
    service::*, stateful_set::*, volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::{types::*, zookeeper_api::*};
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ZookeeperReconcileState {
    pub reconcile_step: ZookeeperReconcileStep,
    pub found_stateful_set_opt: Option<StatefulSetView>,
    pub latest_config_map_rv_opt: Option<StringView>,
}

pub struct ZookeeperReconciler {}

impl Reconciler<ZookeeperClusterView, ZKAPI> for ZookeeperReconciler {
    type T = ZookeeperReconcileState;

    open spec fn reconcile_init_state() -> ZookeeperReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        zk: ZookeeperClusterView, resp_o: Option<ResponseView<ZKAPIOutputView>>, state: ZookeeperReconcileState
    ) -> (ZookeeperReconcileState, Option<RequestView<ZKAPIInputView>>) {
        reconcile_core(zk, resp_o, state)
    }

    open spec fn reconcile_done(state: ZookeeperReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: ZookeeperReconcileState) -> bool {
        reconcile_error(state)
    }
}

pub open spec fn reconcile_init_state() -> ZookeeperReconcileState {
    ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Init,
        found_stateful_set_opt: None,
        latest_config_map_rv_opt: None,
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

pub open spec fn reconcile_core(
    zk: ZookeeperClusterView, resp_o: Option<ResponseView<ZKAPIOutputView>>, state: ZookeeperReconcileState
) -> (ZookeeperReconcileState, Option<RequestView<ZKAPIInputView>>)
    recommends
        zk.well_formed(),
{
    let step = state.reconcile_step;
    let resp = resp_o.get_Some_0();
    let zk_name = zk.metadata.name.get_Some_0();
    let zk_namespace = zk.metadata.namespace.get_Some_0();
    match step {
        ZookeeperReconcileStep::Init => {
            let headless_service = make_headless_service(zk);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: zk_namespace,
                obj: headless_service.to_dynamic_object(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateHeadlessService,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        ZookeeperReconcileStep::AfterCreateHeadlessService => {
            let client_service = make_client_service(zk);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: zk_namespace,
                obj: client_service.to_dynamic_object(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateClientService,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        ZookeeperReconcileStep::AfterCreateClientService => {
            let admin_server_service = make_admin_server_service(zk);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: zk_namespace,
                obj: admin_server_service.to_dynamic_object(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateAdminServerService,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        ZookeeperReconcileStep::AfterCreateAdminServerService => {
            let req_o = APIRequest::GetRequest(GetRequest{
                key: ObjectRef {
                    kind: ConfigMapView::kind(),
                    name: make_config_map_name(zk_name),
                    namespace: zk_namespace,
                }
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterGetConfigMap,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        ZookeeperReconcileStep::AfterGetConfigMap => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_cm_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                if get_cm_resp.is_Ok() {
                    if ConfigMapView::from_dynamic_object(get_cm_resp.get_Ok_0()).is_Ok() {
                        // update
                        let found_config_map = ConfigMapView::from_dynamic_object(get_cm_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            key: make_config_map_key(zk.object_ref()),
                            obj: update_config_map(zk, found_config_map).to_dynamic_object(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterUpdateConfigMap,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_cm_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: zk_namespace,
                        obj: make_config_map(zk).to_dynamic_object(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateConfigMap,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateConfigMap => {
            let create_cm_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            let latest_config_map = ConfigMapView::from_dynamic_object(create_cm_resp.get_Ok_0()).get_Ok_0();
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_cm_resp.is_Ok() && ConfigMapView::from_dynamic_object(create_cm_resp.get_Ok_0()).is_Ok()
            && latest_config_map.metadata.resource_version.is_Some() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: ObjectRef {
                        kind: StatefulSetView::kind(),
                        name: make_stateful_set_name(zk_name),
                        namespace: zk_namespace,
                    }
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet,
                    latest_config_map_rv_opt: Some(int_to_string_view(latest_config_map.metadata.resource_version.get_Some_0())),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterUpdateConfigMap => {
            let update_cm_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            let latest_config_map = ConfigMapView::from_dynamic_object(update_cm_resp.get_Ok_0()).get_Ok_0();
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_cm_resp.is_Ok() && ConfigMapView::from_dynamic_object(update_cm_resp.get_Ok_0()).is_Ok()
            && latest_config_map.metadata.resource_version.is_Some() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: ObjectRef {
                        kind: StatefulSetView::kind(),
                        name: make_stateful_set_name(zk_name),
                        namespace: zk_namespace,
                    }
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet,
                    latest_config_map_rv_opt: Some(int_to_string_view(latest_config_map.metadata.resource_version.get_Some_0())),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterGetStatefulSet => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_sts_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                if get_sts_resp.is_Ok() {
                    if StatefulSetView::from_dynamic_object(get_sts_resp.get_Ok_0()).is_Ok() {
                        let found_stateful_set = StatefulSetView::from_dynamic_object(get_sts_resp.get_Ok_0()).get_Ok_0();
                        // update
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterExistsZKNode,
                            found_stateful_set_opt: Some(found_stateful_set),
                            ..state
                        };
                        let node_path = seq![new_strlit("zookeeper-operator")@, zk_name];
                        let ext_req = ZKAPIInputView::ExistsRequest(
                            zk_name, zk_namespace, node_path
                        );
                        (state_prime, Some(RequestView::ExternalRequest(ext_req)))
                    } else {
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_sts_resp.get_Err_0().is_ObjectNotFound() && state.latest_config_map_rv_opt.is_Some() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                            namespace: zk_namespace,
                            obj: make_stateful_set(zk, state.latest_config_map_rv_opt.get_Some_0()).to_dynamic_object(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateStatefulSet,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterExistsZKNode => {
            let exists_resp = resp.get_ExternalResponse_0().get_ExistsResponse_0().res;
            if resp_o.is_Some() && resp.is_ExternalResponse() && resp.get_ExternalResponse_0().is_ExistsResponse()
            && exists_resp.is_Ok() {
                if exists_resp.get_Ok_0().is_Some() {
                    let version = exists_resp.get_Ok_0().get_Some_0();
                    let node_path = zk_node_path(zk);
                    let data = zk_node_data(zk);
                    let ext_req = ZKAPIInputView::SetDataRequest(
                        zk_name, zk_namespace, node_path, data, version
                    );
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterUpdateZKNode,
                        ..state
                    };
                    (state_prime, Some(RequestView::ExternalRequest(ext_req)))
                } else {
                    let version = exists_resp.get_Ok_0().get_Some_0();
                    let node_path = zk_parent_node_path(zk);
                    let data = new_strlit("")@;
                    let ext_req = ZKAPIInputView::CreateRequest(
                        zk_name, zk_namespace, node_path, data
                    );
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateZKParentNode,
                        ..state
                    };
                    (state_prime, Some(RequestView::ExternalRequest(ext_req)))
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateZKParentNode => {
            let create_resp = resp.get_ExternalResponse_0().get_CreateResponse_0().res;
            if resp_o.is_Some() && resp.is_ExternalResponse() && resp.get_ExternalResponse_0().is_CreateResponse()
            && (create_resp.is_Ok() || create_resp.get_Err_0().is_ZKNodeCreateAlreadyExists()) {
                let node_path = zk_node_path(zk);
                let data = zk_node_data(zk);
                let ext_req = ZKAPIInputView::CreateRequest(
                    zk_name, zk_namespace, node_path, data
                );
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterCreateZKNode,
                    ..state
                };
                (state_prime, Some(RequestView::ExternalRequest(ext_req)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateZKNode => {
            if resp_o.is_Some() && resp.is_ExternalResponse() && resp.get_ExternalResponse_0().is_CreateResponse()
            && resp.get_ExternalResponse_0().get_CreateResponse_0().res.is_Ok()
            && state.found_stateful_set_opt.is_Some() && state.latest_config_map_rv_opt.is_Some() {
                // Only proceed to update the stateful set when zk node is set successfully,
                // otherwise it might cause unsafe downscale.
                let found_stateful_set = state.found_stateful_set_opt.get_Some_0();
                let latest_config_map_rv = state.latest_config_map_rv_opt.get_Some_0();
                let req_o = APIRequest::UpdateRequest(UpdateRequest {
                    key: make_stateful_set_key(zk.object_ref()),
                    obj: update_stateful_set(zk, found_stateful_set, latest_config_map_rv).to_dynamic_object(),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterUpdateStatefulSet,
                    found_stateful_set_opt: None,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterUpdateZKNode => {
            if resp_o.is_Some() && resp.is_ExternalResponse() && resp.get_ExternalResponse_0().is_SetDataResponse()
            && resp.get_ExternalResponse_0().get_SetDataResponse_0().res.is_Ok()
            && state.found_stateful_set_opt.is_Some() && state.latest_config_map_rv_opt.is_Some() {
                // Only proceed to update the stateful set when zk node is set successfully,
                // otherwise it might cause unsafe downscale.
                let found_stateful_set = state.found_stateful_set_opt.get_Some_0();
                let latest_config_map_rv = state.latest_config_map_rv_opt.get_Some_0();
                let req_o = APIRequest::UpdateRequest(UpdateRequest {
                    key: make_stateful_set_key(zk.object_ref()),
                    obj: update_stateful_set(zk, found_stateful_set, latest_config_map_rv).to_dynamic_object(),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterUpdateStatefulSet,
                    found_stateful_set_opt: None,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateStatefulSet => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Done,
                ..state
            };
            (state_prime, None)
        },
        ZookeeperReconcileStep::AfterUpdateStatefulSet => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Done,
                ..state
            };
            (state_prime, None)
        },
        _ => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: step,
                ..state
            };
            (state_prime, None)
        }
    }
}

pub open spec fn reconcile_error_result(state: ZookeeperReconcileState) -> (ZookeeperReconcileState, Option<APIRequest>) {
    let state_prime = ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Error,
        ..state
    };
    (state_prime, None)
}

pub open spec fn zk_node_path(zk: ZookeeperClusterView) -> Seq<StringView>
    recommends
        zk.well_formed(),
{
    seq![new_strlit("zookeeper-operator")@, zk.metadata.name.get_Some_0()]
}

pub open spec fn zk_parent_node_path(zk: ZookeeperClusterView) -> Seq<StringView>
    recommends
        zk.well_formed(),
{
    seq![new_strlit("zookeeper-operator")@]
}

pub open spec fn zk_node_data(zk: ZookeeperClusterView) -> StringView
    recommends
        zk.well_formed(),
{
    new_strlit("CLUSTER_SIZE=")@ + int_to_string_view(zk.spec.replicas)
}

pub open spec fn make_headless_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.well_formed(),
{
    let ports = seq![
        ServicePortView::default().set_name(new_strlit("tcp-client")@).set_port(2181),
        ServicePortView::default().set_name(new_strlit("tcp-quorum")@).set_port(2888),
        ServicePortView::default().set_name(new_strlit("tcp-leader-election")@).set_port(3888),
        ServicePortView::default().set_name(new_strlit("tcp-metrics")@).set_port(7000),
        ServicePortView::default().set_name(new_strlit("tcp-admin-server")@).set_port(8080)
    ];

    make_service(zk, zk.metadata.name.get_Some_0() + new_strlit("-headless")@, ports, false)
}

pub open spec fn make_client_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.well_formed(),
{
    let ports = seq![ServicePortView::default().set_name(new_strlit("tcp-client")@).set_port(2181)];

    make_service(zk, make_client_service_name(zk), ports, true)
}

pub open spec fn make_client_service_name(zk: ZookeeperClusterView) -> StringView
    recommends
        zk.well_formed(),
{
    zk.metadata.name.get_Some_0() + new_strlit("-client")@
}

pub open spec fn make_admin_server_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.well_formed(),
{
    let ports = seq![ServicePortView::default().set_name(new_strlit("tcp-admin-server")@).set_port(8080)];

    make_service(zk, zk.metadata.name.get_Some_0() + new_strlit("-admin-server")@, ports, true)
}

pub open spec fn make_service(
    zk: ZookeeperClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool
) -> ServiceView
    recommends
        zk.well_formed(),
{
    ServiceView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(name)
            .set_labels(Map::empty().insert(new_strlit("app")@, zk.metadata.name.get_Some_0()))
        ).set_spec({
            let spec = ServiceSpecView::default()
                .set_ports(ports)
                .set_selector(Map::empty()
                    .insert(new_strlit("app")@, zk.metadata.name.get_Some_0())
                );
            if !cluster_ip {
                spec.set_cluster_ip(new_strlit("None")@)
            } else {
                spec
            }
        })
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
    ConfigMapView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_config_map_name(zk.metadata.name.get_Some_0()))
            .set_labels(Map::empty().insert(new_strlit("app")@, zk.metadata.name.get_Some_0()))
        )
        .set_data(Map::empty()
            .insert(new_strlit("zoo.cfg")@, make_zk_config(zk))
            .insert(new_strlit("log4j.properties")@, make_log4j_config())
            .insert(new_strlit("log4j-quiet.properties")@, make_log4j_quiet_config())
            .insert(new_strlit("env.sh")@, make_env_config(zk))
        )
}

pub open spec fn update_config_map(zk: ZookeeperClusterView, found_config_map: ConfigMapView) -> ConfigMapView
    recommends
        zk.well_formed(),
{
    found_config_map
        .set_metadata(
            found_config_map.metadata
                .set_labels(make_config_map(zk).metadata.labels.get_Some_0())
        )
        .set_data(make_config_map(zk).data.get_Some_0())
}

pub open spec fn make_zk_config(zk: ZookeeperClusterView) -> StringView {
    new_strlit(
        "4lw.commands.whitelist=cons, envi, conf, crst, srvr, stat, mntr, ruok\n\
        dataDir=/data\n\
        standaloneEnabled=false\n\
        reconfigEnabled=true\n\
        skipACL=yes\n\
        metricsProvider.className=org.apache.zookeeper.metrics.prometheus.PrometheusMetricsProvider\n\
        metricsProvider.httpPort=7000\n\
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
        zk.well_formed(),
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
        CLUSTER_SIZE=")@ + int_to_string_view(zk.spec.replicas) + new_strlit("\n")@
}

pub open spec fn make_stateful_set_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: StatefulSetView::kind(),
        name: make_stateful_set_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn make_stateful_set_name(zk_name: StringView) -> StringView {
    zk_name
}

pub open spec fn update_stateful_set(zk: ZookeeperClusterView, found_stateful_set: StatefulSetView, rv: StringView) -> StatefulSetView
    recommends
        zk.well_formed(),
{
    found_stateful_set
        .set_metadata(
            found_stateful_set.metadata
                .set_labels(make_stateful_set(zk, rv).metadata.labels.get_Some_0())
        )
        .set_spec(make_stateful_set(zk, rv).spec.get_Some_0())
}

pub open spec fn make_stateful_set(zk: ZookeeperClusterView, rv: StringView) -> StatefulSetView
    recommends
        zk.well_formed(),
{
    let name = make_stateful_set_name(zk.metadata.name.get_Some_0());
    let namespace = zk.metadata.namespace.get_Some_0();

    let labels = Map::empty().insert(new_strlit("app")@, zk.metadata.name.get_Some_0());
    let metadata = ObjectMetaView::default()
        .set_name(name)
        .set_labels(labels);

    let spec = StatefulSetSpecView::default()
        .set_replicas(zk.spec.replicas)
        .set_service_name(name + new_strlit("-headless")@)
        .set_selector(LabelSelectorView::default().set_match_labels(labels))
        .set_template(PodTemplateSpecView::default()
            .set_metadata(ObjectMetaView::default()
                .set_generate_name(name)
                .set_labels(
                    Map::empty()
                        .insert(new_strlit("app")@, zk.metadata.name.get_Some_0())
                        .insert(new_strlit("kind")@, new_strlit("ZookeeperMember")@)
                )
                .set_annotations(
                    Map::empty()
                        .insert(new_strlit("config")@, rv)
                )
            )
            .set_spec(make_zk_pod_spec(zk))
        )
        .set_pvc_retention_policy(StatefulSetPersistentVolumeClaimRetentionPolicyView::default()
            .set_when_deleted(new_strlit("Delete")@)
            .set_when_scaled(new_strlit("Delete")@)
        )
        .set_volume_claim_templates(seq![
            PersistentVolumeClaimView::default()
                .set_metadata(ObjectMetaView::default()
                    .set_name(new_strlit("data")@)
                    .set_labels(labels)
                )
                .set_spec(PersistentVolumeClaimSpecView::default()
                    .set_access_modes(seq![new_strlit("ReadWriteOnce")@])
                )
        ]);

    StatefulSetView::default().set_metadata(metadata).set_spec(spec)
}

pub open spec fn make_zk_pod_spec(zk: ZookeeperClusterView) -> PodSpecView
    recommends
        zk.well_formed(),
{
    PodSpecView::default()
        .set_containers(seq![
            ContainerView::default()
                .set_name(new_strlit("zookeeper")@)
                .set_image(zk.spec.image)
                .set_lifecycle(LifecycleView::default()
                    .set_pre_stop(LifecycleHandlerView::default()
                        .set_exec(
                            ExecActionView::default()
                                .set_command(seq![new_strlit("zookeeperTeardown.sh")@])
                        )
                    )
                )
                .set_volume_mounts(seq![
                    VolumeMountView::default()
                        .set_name(new_strlit("data")@)
                        .set_mount_path(new_strlit("/data")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("conf")@)
                        .set_mount_path(new_strlit("/conf")@),
                ])
                .set_ports(seq![
                    ContainerPortView::default().set_name(new_strlit("client")@).set_container_port(2181),
                    ContainerPortView::default().set_name(new_strlit("quorum")@).set_container_port(2888),
                    ContainerPortView::default().set_name(new_strlit("leader-election")@).set_container_port(3888),
                    ContainerPortView::default().set_name(new_strlit("metrics")@).set_container_port(7000),
                    ContainerPortView::default().set_name(new_strlit("admin-server")@).set_container_port(8080)
                ])
                .set_readiness_probe(
                    ProbeView::default()
                        .set_exec(
                            ExecActionView::default()
                                .set_command(seq![new_strlit("zookeeperReady.sh")@])
                        )
                        .set_failure_threshold(3)
                        .set_initial_delay_seconds(10)
                        .set_period_seconds(10)
                        .set_success_threshold(1)
                        .set_timeout_seconds(10)
                )
                .set_liveness_probe(
                    ProbeView::default()
                        .set_exec(
                            ExecActionView::default()
                                .set_command(seq![new_strlit("zookeeperLive.sh")@])
                        )
                        .set_failure_threshold(3)
                        .set_initial_delay_seconds(10)
                        .set_period_seconds(10)
                        .set_success_threshold(1)
                        .set_timeout_seconds(10)
                )
        ])
        .set_volumes(seq![
            VolumeView::default().set_name(new_strlit("conf")@).set_config_map(
                ConfigMapVolumeSourceView::default().set_name(zk.metadata.name.get_Some_0() + new_strlit("-configmap")@)
            )
        ])
}

}
