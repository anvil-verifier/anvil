// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*, volume_resource_requirements::*,
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
        if state.latest_config_map_rv_opt is Some {
            Ok(make_stateful_set(zk, state.latest_config_map_rv_opt->0).marshal())
        } else {
            Err(())
        }
    }

    open spec fn update(zk: ZookeeperClusterView, state: ZookeeperReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let sts = StatefulSetView::unmarshal(obj);
        let found_sts = sts->Ok_0;
        if sts is Ok && found_sts.metadata.owner_references_only_contains(zk.controller_owner_ref())
        && state.latest_config_map_rv_opt is Some && found_sts.spec is Some {
            Ok(update_stateful_set(zk, found_sts, state.latest_config_map_rv_opt->0).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(zk: ZookeeperClusterView, obj: DynamicObjectView, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<APIRequest>), ()>) {
        let sts_obj = StatefulSetView::unmarshal(obj);
        if sts_obj is Ok {
            let req = APIRequest::UpdateStatusRequest(UpdateStatusRequest {
                namespace: zk.metadata.namespace->0,
                name: zk.metadata.name->0,
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
        if sts_obj is Ok {
            let stateful_set = sts_obj->Ok_0;
            let ready_replicas = if stateful_set.status is Some && stateful_set.status->0.ready_replicas is Some {
                stateful_set.status->0.ready_replicas->0
            } else {
                0
            };
            let req = APIRequest::UpdateStatusRequest(UpdateStatusRequest {
                namespace: zk.metadata.namespace->0,
                name: zk.metadata.name->0,
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
        namespace: zk.metadata.namespace->0,
    }
}

pub open spec fn make_stateful_set_name(zk: ZookeeperClusterView) -> StringView { zk.metadata.name->0 }

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
            replicas: make_stateful_set(zk, rv).spec->0.replicas,
            template: make_stateful_set(zk, rv).spec->0.template,
            persistent_volume_claim_retention_policy: make_stateful_set(zk, rv).spec->0.persistent_volume_claim_retention_policy,
            ..found_stateful_set.spec->0
        }),
        ..found_stateful_set
    }
}

pub open spec fn make_stateful_set(zk: ZookeeperClusterView, rv: StringView) -> StatefulSetView {
    let name = make_stateful_set_name(zk);
    let namespace = zk.metadata.namespace->0;

    let metadata = ObjectMetaView::default()
        .with_name(name)
        .with_labels(make_labels(zk))
        .with_annotations(zk.spec.annotations)
        .with_owner_references(make_owner_references(zk));

    let spec = StatefulSetSpecView::default()
        .with_replicas(zk.spec.replicas)
        .with_service_name(name + "-headless"@)
        .with_selector(LabelSelectorView::default().with_match_labels(make_base_labels(zk)))
        .with_template(PodTemplateSpecView::default()
            .with_metadata(ObjectMetaView::default()
                .with_labels(make_labels(zk))
                .with_annotations(zk.spec.annotations.insert("anvil.dev/lastRestartAt"@, rv))
            )
            .with_spec(make_zk_pod_spec(zk))
        )
        .with_pvc_retention_policy(StatefulSetPersistentVolumeClaimRetentionPolicyView::default()
            .with_when_deleted("Delete"@)
            .with_when_scaled("Delete"@)
        )
        .with_volume_claim_templates({
            if zk.spec.persistence.enabled {
                seq![
                    PersistentVolumeClaimView::default()
                    .with_metadata(ObjectMetaView::default()
                        .with_name("data"@)
                        .with_labels(make_base_labels(zk))
                    )
                    .with_spec(PersistentVolumeClaimSpecView::default()
                        .with_access_modes(seq!["ReadWriteOnce"@])
                        .with_resources(VolumeResourceRequirementsView::default()
                            .with_requests(Map::empty()
                                .insert("storage"@, zk.spec.persistence.storage_size)
                            )
                        )
                        .with_storage_class_name(zk.spec.persistence.storage_class_name)
                    )
                ]
            } else {
                seq![]
            }
        });

    StatefulSetView::default().with_metadata(metadata).with_spec(spec)
}

pub open spec fn make_zk_pod_spec(zk: ZookeeperClusterView) -> PodSpecView {
    PodSpecView {
        affinity: zk.spec.affinity,
        containers: seq![
            ContainerView {
                name: "zookeeper"@,
                image: Some(zk.spec.image),
                command: Some(seq!["/usr/local/bin/zookeeperStart.sh"@]),
                lifecycle: Some(LifecycleView::default()
                    .with_pre_stop(LifecycleHandlerView::default()
                        .with_exec(
                            ExecActionView::default()
                                .with_command(seq!["zookeeperTeardown.sh"@])
                        )
                    )
                ),
                image_pull_policy: Some("Always"@),
                resources: zk.spec.resources,
                volume_mounts: Some(seq![
                    VolumeMountView::default()
                        .with_name("data"@)
                        .with_mount_path("/data"@),
                    VolumeMountView::default()
                        .with_name("conf"@)
                        .with_mount_path("/conf"@),
                ]),
                ports: Some(seq![
                    ContainerPortView::default().with_name("client"@).with_container_port(zk.spec.ports.client),
                    ContainerPortView::default().with_name("quorum"@).with_container_port(zk.spec.ports.quorum),
                    ContainerPortView::default().with_name("leader-election"@).with_container_port(zk.spec.ports.leader_election),
                    ContainerPortView::default().with_name("metrics"@).with_container_port(zk.spec.ports.metrics),
                    ContainerPortView::default().with_name("admin-server"@).with_container_port(zk.spec.ports.admin_server)
                ]),
                readiness_probe: Some(ProbeView::default()
                    .with_exec(
                        ExecActionView::default()
                            .with_command(seq!["zookeeperReady.sh"@])
                    )
                    .with_failure_threshold(3)
                    .with_initial_delay_seconds(10)
                    .with_period_seconds(10)
                    .with_success_threshold(1)
                    .with_timeout_seconds(10)
                ),
                liveness_probe: Some(ProbeView::default()
                    .with_exec(
                        ExecActionView::default()
                            .with_command(seq!["zookeeperLive.sh"@])
                    )
                    .with_failure_threshold(3)
                    .with_initial_delay_seconds(10)
                    .with_period_seconds(10)
                    .with_success_threshold(1)
                    .with_timeout_seconds(10)
                ),
                ..ContainerView::default()
            }
        ],
        volumes: Some({
            let volumes = seq![
                VolumeView::default().with_name("conf"@).with_config_map(
                    ConfigMapVolumeSourceView::default().with_name(zk.metadata.name->0 + "-configmap"@)
                )
            ];
            if zk.spec.persistence.enabled {
                volumes
            } else {
                volumes.push(VolumeView::default().with_name("data"@).with_empty_dir(EmptyDirVolumeSourceView::default()))
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
