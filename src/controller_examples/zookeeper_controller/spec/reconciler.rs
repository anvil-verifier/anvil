// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, error::*, label_selector::*, object_meta::*,
    persistent_volume_claim::*, pod::*, pod_template_spec::*, resource::*, service::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::{zookeeper_api::*, zookeepercluster::*};
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ZookeeperReconcileState {
    pub reconcile_step: ZookeeperReconcileStep,
    pub sts_from_get: Option<StatefulSetView>,
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
        sts_from_get: None,
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
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let step = state.reconcile_step;
    match step {
        ZookeeperReconcileStep::Init => {
            let headless_service = make_headless_service(zk);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: zk.metadata.namespace.get_Some_0(),
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
                namespace: zk.metadata.namespace.get_Some_0(),
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
                namespace: zk.metadata.namespace.get_Some_0(),
                obj: admin_server_service.to_dynamic_object(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateAdminServerService,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        ZookeeperReconcileStep::AfterCreateAdminServerService => {
            let config_map = make_config_map(zk);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: zk.metadata.namespace.get_Some_0(),
                obj: config_map.to_dynamic_object(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateConfigMap,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        ZookeeperReconcileStep::AfterCreateConfigMap => {
            let req_o = APIRequest::GetRequest(GetRequest{
                key: ObjectRef {
                    kind: StatefulSetView::kind(),
                    name: make_stateful_set_name(zk.metadata.name.get_Some_0()),
                    namespace: zk.metadata.namespace.get_Some_0(),
                }
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        ZookeeperReconcileStep::AfterGetStatefulSet => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse()
            && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let get_sts_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_sts_resp.is_Ok() {
                    // update
                    if StatefulSetView::from_dynamic_object(get_sts_resp.get_Ok_0()).is_Ok() {
                        let found_stateful_set = StatefulSetView::from_dynamic_object(get_sts_resp.get_Ok_0()).get_Ok_0();
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterSetZKNode,
                            sts_from_get: Some(found_stateful_set),
                            ..state
                        };
                        let ext_req = ZKAPIInputView::ReconcileZKNode(
                            zk.metadata.name.get_Some_0(), zk.metadata.namespace.get_Some_0(), int_to_string_view(zk.spec.replicas)
                        );
                        (state_prime, Some(RequestView::ExternalRequest(ext_req)))
                    } else {
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_sts_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                            namespace: zk.metadata.namespace.get_Some_0(),
                            obj: make_stateful_set(zk).to_dynamic_object(),
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
        ZookeeperReconcileStep::AfterSetZKNode => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_ExternalResponse()
            && resp_o.get_Some_0().get_ExternalResponse_0().is_ReconcileZKNode()
            && state.sts_from_get.is_Some(){
                let found_stateful_set = state.sts_from_get.get_Some_0();
                let req_o = APIRequest::UpdateRequest(UpdateRequest {
                    key: make_stateful_set_key(zk.object_ref()),
                    obj: update_stateful_set(zk, found_stateful_set).to_dynamic_object(),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterUpdateStatefulSet,
                    sts_from_get: None,
                };
                (state_prime,  Some(RequestView::KRequest(req_o)))
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

pub open spec fn make_headless_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
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
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let ports = seq![ServicePortView::default().set_name(new_strlit("tcp-client")@).set_port(2181)];

    make_service(zk, make_client_service_name(zk), ports, true)
}

pub open spec fn make_client_service_name(zk: ZookeeperClusterView) -> StringView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    zk.metadata.name.get_Some_0() + new_strlit("-client")@
}

pub open spec fn make_admin_server_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let ports = seq![ServicePortView::default().set_name(new_strlit("tcp-admin-server")@).set_port(8080)];

    make_service(zk, zk.metadata.name.get_Some_0() + new_strlit("-admin-server")@, ports, true)
}

pub open spec fn make_service(
    zk: ZookeeperClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool
) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
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

pub open spec fn make_config_map(zk: ZookeeperClusterView) -> ConfigMapView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    ConfigMapView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(zk.metadata.name.get_Some_0() + new_strlit("-configmap")@)
            .set_labels(Map::empty().insert(new_strlit("app")@, zk.metadata.name.get_Some_0()))
        )
        .set_data(Map::empty()
            .insert(new_strlit("zoo.cfg")@, make_zk_config())
            .insert(new_strlit("log4j.properties")@, make_log4j_config())
            .insert(new_strlit("log4j-quiet.properties")@, make_log4j_quiet_config())
            .insert(new_strlit("env.sh")@, make_env_config(zk))
        )
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

pub open spec fn update_stateful_set(zk: ZookeeperClusterView, found_stateful_set: StatefulSetView) -> StatefulSetView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    found_stateful_set.set_spec(make_stateful_set(zk).spec.get_Some_0())
}

pub open spec fn make_stateful_set(zk: ZookeeperClusterView) -> StatefulSetView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
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
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    PodSpecView::default()
        .set_containers(seq![
            ContainerView::default()
                .set_name(new_strlit("zookeeper")@)
                .set_image(new_strlit("pravega/zookeeper:0.2.14")@)
                .set_lifecycle(LifecycleView::default()
                    .set_pre_stop(LifecycleHandlerView::default()
                        .set_exec(seq![new_strlit("zookeeperTeardown.sh")@])
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
        ])
        .set_volumes(seq![
            VolumeView::default().set_name(new_strlit("conf")@).set_config_map(
                ConfigMapVolumeSourceView::default().set_name(zk.metadata.name.get_Some_0() + new_strlit("-configmap")@)
            )
        ])
}

}
