// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::spec::resource::service_account::make_service_account_name;
use crate::fluent_controller::fluentbit::spec::types::*;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct DaemonSetBuilder {}

impl ResourceBuilder<FluentBitView, FluentBitReconcileState> for DaemonSetBuilder {
    open spec fn get_request(fb: FluentBitView) -> GetRequest {
        GetRequest { key: make_daemon_set_key(fb) }
    }

    open spec fn make(fb: FluentBitView, state: FluentBitReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_daemon_set(fb).marshal())
    }

    open spec fn update(fb: FluentBitView, state: FluentBitReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let ds = DaemonSetView::unmarshal(obj);
        let found_ds = ds.get_Ok_0();
        if ds.is_Ok() && found_ds.metadata.owner_references_only_contains(fb.controller_owner_ref()) && found_ds.spec.is_Some() {
            Ok(update_daemon_set(fb, found_ds).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
        let ds = DaemonSetView::unmarshal(obj);
        if ds.is_Ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
        let ds = DaemonSetView::unmarshal(obj);
        if ds.is_Ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }

    open spec fn unchangeable(object: DynamicObjectView, fb: FluentBitView) -> bool {
        true
    }
}

pub open spec fn make_daemon_set_key(fb: FluentBitView) -> ObjectRef
    recommends
        fb.well_formed(),
{
    ObjectRef {
        kind: DaemonSetView::kind(),
        name: make_daemon_set_name(fb),
        namespace: fb.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn make_daemon_set_name(fb: FluentBitView) -> StringView
    recommends
        fb.well_formed(),
{
    fb.metadata.name.get_Some_0()
}

pub open spec fn update_daemon_set(fb: FluentBitView, found_daemon_set: DaemonSetView) -> DaemonSetView
    recommends
        fb.well_formed(),
        found_daemon_set.spec.is_Some(),
{
    let made_spec = make_daemon_set(fb).spec.get_Some_0();
    DaemonSetView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(fb)),
            finalizers: None,
            labels: make_daemon_set(fb).metadata.labels,
            annotations: make_daemon_set(fb).metadata.annotations,
            ..found_daemon_set.metadata
        },
        spec: Some(DaemonSetSpecView {
            template: made_spec.template,
            ..found_daemon_set.spec.get_Some_0()
        }),
        ..found_daemon_set
    }
}

pub open spec fn make_daemon_set(fb: FluentBitView) -> DaemonSetView
    recommends
        fb.well_formed(),
{
    DaemonSetView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_daemon_set_name(fb))
            .set_labels(make_labels(fb))
            .set_annotations(fb.spec.annotations)
            .set_owner_references(make_owner_references(fb))
        ).set_spec(DaemonSetSpecView::default()
            .set_selector(LabelSelectorView::default().set_match_labels(make_base_labels(fb)))
            .set_template(PodTemplateSpecView::default()
                .set_metadata(ObjectMetaView::default()
                    .set_labels(make_labels(fb))
                    .set_annotations(fb.spec.annotations)
                )
                .set_spec(make_fluentbit_pod_spec(fb))
            )
        )
}

pub open spec fn make_fluentbit_pod_spec(fb: FluentBitView) -> PodSpecView
    recommends
        fb.well_formed(),
{
    PodSpecView {
        service_account_name: Some(make_service_account_name(fb)),
        volumes: Some(seq![
            VolumeView::default()
                .set_name(new_strlit("varlibcontainers")@)
                .set_host_path(HostPathVolumeSourceView::default()
                    .set_path(new_strlit("/containers")@)
                ),
            VolumeView::default()
                .set_name(new_strlit("config")@)
                .set_secret(SecretVolumeSourceView::default()
                    .set_secret_name(fb.spec.fluentbit_config_name)
                ),
            VolumeView::default()
                .set_name(new_strlit("varlogs")@)
                .set_host_path(HostPathVolumeSourceView::default()
                    .set_path(new_strlit("/var/log")@)
                ),
            VolumeView::default()
                .set_name(new_strlit("systemd")@)
                .set_host_path(HostPathVolumeSourceView::default()
                    .set_path(new_strlit("/var/log/journal")@)
                ),
            VolumeView::default()
                .set_name(new_strlit("positions")@)
                .set_host_path(HostPathVolumeSourceView::default()
                    .set_path(new_strlit("/var/lib/fluent-bit/")@)
                ),
        ]),
        containers: seq![
            ContainerView {
                name: new_strlit("fluent-bit")@,
                image: Some(fb.spec.image),
                env: Some(make_env(fb)),
                volume_mounts: Some(seq![
                    VolumeMountView {
                        name: new_strlit("varlibcontainers")@,
                        read_only: Some(true),
                        mount_path: new_strlit("/containers")@,
                        mount_propagation: fb.spec.internal_mount_propagation,
                        ..VolumeMountView::default()
                    },
                    VolumeMountView {
                        name: new_strlit("config")@,
                        read_only: Some(true),
                        mount_path: new_strlit("/fluent-bit/config")@,
                        ..VolumeMountView::default()
                    },
                    VolumeMountView {
                        name: new_strlit("varlogs")@,
                        read_only: Some(true),
                        mount_path: new_strlit("/var/log/")@,
                        mount_propagation: fb.spec.internal_mount_propagation,
                        ..VolumeMountView::default()
                    },
                    VolumeMountView {
                        name: new_strlit("systemd")@,
                        read_only: Some(true),
                        mount_path: new_strlit("/var/log/journal")@,
                        mount_propagation: fb.spec.internal_mount_propagation,
                        ..VolumeMountView::default()
                    },
                    VolumeMountView {
                        name: new_strlit("positions")@,
                        mount_path: new_strlit("/fluent-bit/tail")@,
                        ..VolumeMountView::default()
                    },
                ]),
                ports: Some(seq![
                    ContainerPortView::default()
                        .set_name(new_strlit("metrics")@)
                        .set_container_port({
                            let port = if fb.spec.metrics_port.is_Some() { fb.spec.metrics_port.get_Some_0() } else { 2020 };
                            port
                        }),
                ]),
                resources: fb.spec.resources,
                ..ContainerView::default()
            }
        ],
        tolerations: fb.spec.tolerations,
        affinity: fb.spec.affinity,
        node_selector: Some(fb.spec.node_selector),
        runtime_class_name: fb.spec.runtime_class_name,
        dns_policy: fb.spec.dns_policy,
        priority_class_name: fb.spec.priority_class_name,
        scheduler_name: fb.spec.scheduler_name,
        security_context: fb.spec.security_context,
        ..PodSpecView::default()
    }
}

pub open spec fn make_env(fluentbit: FluentBitView) -> Seq<EnvVarView> {
    seq![
        EnvVarView {
            name: new_strlit("NODE_NAME")@,
            value_from: Some(EnvVarSourceView {
                field_ref: Some(ObjectFieldSelectorView {
                    field_path: new_strlit("spec.nodeName")@,
                    ..ObjectFieldSelectorView::default()
                }),
                ..EnvVarSourceView::default()
            }),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("HOST_IP")@,
            value_from: Some(EnvVarSourceView {
                field_ref: Some(ObjectFieldSelectorView {
                    field_path: new_strlit("status.hostIP")@,
                    ..ObjectFieldSelectorView::default()
                }),
                ..EnvVarSourceView::default()
            }),
            ..EnvVarView::default()
        },
    ]
}


}
