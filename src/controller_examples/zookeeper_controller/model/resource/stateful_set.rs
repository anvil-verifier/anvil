// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use crate::zookeeper_controller::model::resource::{common::*, config_map::make_config_map_key};
use crate::zookeeper_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct StatefulSetBuilder {}

impl ResourceBuilder<ZookeeperClusterView, ZookeeperReconcileState> for StatefulSetBuilder {
    open spec fn get_request(zk: ZookeeperClusterView) -> GetRequest {
        GetRequest { key: make_stateful_set_key(zk) }
    }

    open spec fn make(zk: ZookeeperClusterView, state: ZookeeperReconcileState) -> Result<DynamicObjectView, ()> {
        if state.latest_config_map_rv_opt.is_Some() {
            Ok(make_stateful_set(zk, state.latest_config_map_rv_opt.get_Some_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn update(zk: ZookeeperClusterView, state: ZookeeperReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let sts = StatefulSetView::unmarshal(obj);
        let found_sts = sts.get_Ok_0();
        if sts.is_Ok() && found_sts.metadata.owner_references_only_contains(zk.controller_owner_ref())
        && state.latest_config_map_rv_opt.is_Some() && found_sts.spec.is_Some() {
            Ok(update_stateful_set(zk, found_sts, state.latest_config_map_rv_opt.get_Some_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(zk: ZookeeperClusterView, obj: DynamicObjectView, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<APIRequest>), ()>) {
        let sts_obj = StatefulSetView::unmarshal(obj);
        if sts_obj.is_Ok() {
            let req = APIRequest::UpdateStatusRequest(UpdateStatusRequest {
                namespace: zk.metadata.namespace.get_Some_0(),
                name: zk.metadata.name.get_Some_0(),
                obj: update_zk_status(zk, 0).marshal(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterUpdateStatus,
                ..state
            };
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(zk: ZookeeperClusterView, obj: DynamicObjectView, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<APIRequest>), ()>) {
        let sts_obj = StatefulSetView::unmarshal(obj);
        if sts_obj.is_Ok() {
            let stateful_set = sts_obj.get_Ok_0();
            let ready_replicas = if stateful_set.status.is_Some() && stateful_set.status.get_Some_0().ready_replicas.is_Some() {
                stateful_set.status.get_Some_0().ready_replicas.get_Some_0()
            } else {
                0
            };
            let req = APIRequest::UpdateStatusRequest(UpdateStatusRequest {
                namespace: zk.metadata.namespace.get_Some_0(),
                name: zk.metadata.name.get_Some_0(),
                obj: update_zk_status(zk, ready_replicas).marshal(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterUpdateStatus,
                ..state
            };
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_stateful_set_key(zk: ZookeeperClusterView) -> ObjectRef {
    ObjectRef {
        kind: StatefulSetView::kind(),
        name: make_stateful_set_name(zk),
        namespace: zk.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn make_stateful_set_name(zk: ZookeeperClusterView) -> StringView { zk.metadata.name.get_Some_0() }

pub open spec fn update_stateful_set(zk: ZookeeperClusterView, found_stateful_set: StatefulSetView, rv: StringView) -> StatefulSetView {
    StatefulSetView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(zk)),
            finalizers: None,
            labels: make_stateful_set(zk, rv).metadata.labels,
            annotations: make_stateful_set(zk, rv).metadata.annotations,
            ..found_stateful_set.metadata
        },
        spec: Some(StatefulSetSpecView {
            replicas: make_stateful_set(zk, rv).spec.get_Some_0().replicas,
            template: make_stateful_set(zk, rv).spec.get_Some_0().template,
            persistent_volume_claim_retention_policy: make_stateful_set(zk, rv).spec.get_Some_0().persistent_volume_claim_retention_policy,
            ..found_stateful_set.spec.get_Some_0()
        }),
        ..found_stateful_set
    }
}

pub open spec fn make_stateful_set(zk: ZookeeperClusterView, rv: StringView) -> StatefulSetView {
    let name = make_stateful_set_name(zk);
    let namespace = zk.metadata.namespace.get_Some_0();

    let metadata = ObjectMetaView::default()
        .set_name(name)
        .set_labels(make_labels(zk))
        .set_annotations(zk.spec.annotations)
        .set_owner_references(make_owner_references(zk));

    let spec = StatefulSetSpecView::default()
        .set_replicas(zk.spec.replicas)
        .set_service_name(name + new_strlit("-headless")@)
        .set_selector(LabelSelectorView::default().set_match_labels(make_base_labels(zk)))
        .set_template(PodTemplateSpecView::default()
            .set_metadata(ObjectMetaView::default()
                .set_labels(make_labels(zk))
                .set_annotations(zk.spec.annotations.insert(new_strlit("anvil.dev/lastRestartAt")@, rv))
            )
            .set_spec(make_zk_pod_spec(zk))
        )
        .set_pvc_retention_policy(StatefulSetPersistentVolumeClaimRetentionPolicyView::default()
            .set_when_deleted(new_strlit("Delete")@)
            .set_when_scaled(new_strlit("Delete")@)
        )
        .set_volume_claim_templates({
            if zk.spec.persistence.enabled {
                seq![
                    PersistentVolumeClaimView::default()
                    .set_metadata(ObjectMetaView::default()
                        .set_name(new_strlit("data")@)
                        .set_labels(make_base_labels(zk))
                    )
                    .set_spec(PersistentVolumeClaimSpecView::default()
                        .set_access_modes(seq![new_strlit("ReadWriteOnce")@])
                        .set_resources(ResourceRequirementsView::default()
                            .set_requests(Map::empty()
                                .insert(new_strlit("storage")@, zk.spec.persistence.storage_size)
                            )
                        )
                        .set_storage_class_name(zk.spec.persistence.storage_class_name)
                    )
                ]
            } else {
                seq![]
            }
        });

    StatefulSetView::default().set_metadata(metadata).set_spec(spec)
}

pub open spec fn make_zk_pod_spec(zk: ZookeeperClusterView) -> PodSpecView {
    PodSpecView {
        affinity: zk.spec.affinity,
        containers: seq![
            ContainerView {
                name: new_strlit("zookeeper")@,
                image: Some(zk.spec.image),
                command: Some(seq![new_strlit("/usr/local/bin/zookeeperStart.sh")@]),
                lifecycle: Some(LifecycleView::default()
                    .set_pre_stop(LifecycleHandlerView::default()
                        .set_exec(
                            ExecActionView::default()
                                .set_command(seq![new_strlit("zookeeperTeardown.sh")@])
                        )
                    )
                ),
                image_pull_policy: Some(new_strlit("Always")@),
                resources: zk.spec.resources,
                volume_mounts: Some(seq![
                    VolumeMountView::default()
                        .set_name(new_strlit("data")@)
                        .set_mount_path(new_strlit("/data")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("conf")@)
                        .set_mount_path(new_strlit("/conf")@),
                ]),
                ports: Some(seq![
                    ContainerPortView::default().set_name(new_strlit("client")@).set_container_port(zk.spec.ports.client),
                    ContainerPortView::default().set_name(new_strlit("quorum")@).set_container_port(zk.spec.ports.quorum),
                    ContainerPortView::default().set_name(new_strlit("leader-election")@).set_container_port(zk.spec.ports.leader_election),
                    ContainerPortView::default().set_name(new_strlit("metrics")@).set_container_port(zk.spec.ports.metrics),
                    ContainerPortView::default().set_name(new_strlit("admin-server")@).set_container_port(zk.spec.ports.admin_server)
                ]),
                readiness_probe: Some(ProbeView::default()
                    .set_exec(
                        ExecActionView::default()
                            .set_command(seq![new_strlit("zookeeperReady.sh")@])
                    )
                    .set_failure_threshold(3)
                    .set_initial_delay_seconds(10)
                    .set_period_seconds(10)
                    .set_success_threshold(1)
                    .set_timeout_seconds(10)
                ),
                liveness_probe: Some(ProbeView::default()
                    .set_exec(
                        ExecActionView::default()
                            .set_command(seq![new_strlit("zookeeperLive.sh")@])
                    )
                    .set_failure_threshold(3)
                    .set_initial_delay_seconds(10)
                    .set_period_seconds(10)
                    .set_success_threshold(1)
                    .set_timeout_seconds(10)
                ),
                ..ContainerView::default()
            }
        ],
        volumes: Some({
            let volumes = seq![
                VolumeView::default().set_name(new_strlit("conf")@).set_config_map(
                    ConfigMapVolumeSourceView::default().set_name(zk.metadata.name.get_Some_0() + new_strlit("-configmap")@)
                )
            ];
            if zk.spec.persistence.enabled {
                volumes
            } else {
                volumes.push(VolumeView::default().set_name(new_strlit("data")@).set_empty_dir(EmptyDirVolumeSourceView::default()))
            }
        }),
        tolerations: zk.spec.tolerations,
        node_selector: Some(zk.spec.node_selector),
        ..PodSpecView::default()
    }
}

pub open spec fn update_zk_status(zk: ZookeeperClusterView, ready_replicas: int) -> ZookeeperClusterView {
    ZookeeperClusterView {
        status: Some(ZookeeperClusterStatusView {
            ready_replicas: ready_replicas,
        }),
        ..zk
    }
}

}
