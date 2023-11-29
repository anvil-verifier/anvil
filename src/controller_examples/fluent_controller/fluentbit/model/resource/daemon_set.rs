// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::model::resource::{
    common::*, service_account::make_service_account_name,
};
use crate::fluent_controller::fluentbit::trusted::{spec_types::*, step::*};
use crate::kubernetes_api_objects::spec::{
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
}

pub open spec fn make_daemon_set_key(fb: FluentBitView) -> ObjectRef {
    ObjectRef {
        kind: DaemonSetView::kind(),
        name: make_daemon_set_name(fb),
        namespace: fb.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn make_daemon_set_name(fb: FluentBitView) -> StringView { fb.metadata.name.get_Some_0() }

pub open spec fn update_daemon_set(fb: FluentBitView, found_daemon_set: DaemonSetView) -> DaemonSetView {
    DaemonSetView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(fb)),
            finalizers: None,
            labels: make_daemon_set(fb).metadata.labels,
            annotations: make_daemon_set(fb).metadata.annotations,
            ..found_daemon_set.metadata
        },
        spec: Some(DaemonSetSpecView {
            template: make_daemon_set(fb).spec.get_Some_0().template,
            ..found_daemon_set.spec.get_Some_0()
        }),
        ..found_daemon_set
    }
}

pub open spec fn make_daemon_set(fb: FluentBitView) -> DaemonSetView {
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

pub open spec fn make_fluentbit_pod_spec(fb: FluentBitView) -> PodSpecView {
    PodSpecView {
        service_account_name: Some(make_service_account_name(fb)),
        image_pull_secrets: if fb.spec.image_pull_secrets.is_Some() {
                fb.spec.image_pull_secrets
            } else {
                PodSpecView::default().image_pull_secrets
            },
        init_containers: if fb.spec.init_containers.is_Some() {
                fb.spec.init_containers
            } else {
                PodSpecView::default().init_containers
            },
        volumes: Some({
            let config_volume = VolumeView::default().set_name(new_strlit("config")@)
                    .set_secret(SecretVolumeSourceView::default().set_secret_name(fb.spec.fluentbit_config_name));
            let varlibcontainers_volume = VolumeView::default().set_name(new_strlit("varlibcontainers")@)
                    .set_host_path(HostPathVolumeSourceView::default().set_path({
                        if fb.spec.container_log_real_path.is_Some() {
                            fb.spec.container_log_real_path.get_Some_0()
                        } else { new_strlit("/containers")@ }
                    }));
            let varlogs_volume = VolumeView::default().set_name(new_strlit("varlogs")@)
                    .set_host_path(HostPathVolumeSourceView::default().set_path(new_strlit("/var/log")@));
            let systemd_volume = VolumeView::default().set_name(new_strlit("systemd")@)
                    .set_host_path(HostPathVolumeSourceView::default().set_path(new_strlit("/var/log/journal")@));
            if fb.spec.position_db.is_Some() {
                let positions_volume = VolumeView::default().set_name(new_strlit("positions")@)
                    .set_host_path(fb.spec.position_db.get_Some_0());
                if !fb.spec.disable_log_volumes && fb.spec.volumes.is_Some() {
                    fb.spec.volumes.get_Some_0().push(config_volume).push(varlibcontainers_volume).push(varlogs_volume)
                        .push(systemd_volume).push(positions_volume)
                } else if !fb.spec.disable_log_volumes {
                    seq![config_volume, varlibcontainers_volume, varlogs_volume, systemd_volume, positions_volume]
                } else if fb.spec.volumes.is_Some() {
                    fb.spec.volumes.get_Some_0().push(config_volume).push(positions_volume)
                } else {
                    seq![config_volume, positions_volume]
                }
            } else {
                if !fb.spec.disable_log_volumes && fb.spec.volumes.is_Some() {
                    fb.spec.volumes.get_Some_0().push(config_volume).push(varlibcontainers_volume).push(varlogs_volume).push(systemd_volume)
                } else if !fb.spec.disable_log_volumes {
                    seq![config_volume, varlibcontainers_volume, varlogs_volume, systemd_volume]
                } else if fb.spec.volumes.is_Some() {
                    fb.spec.volumes.get_Some_0().push(config_volume)
                } else {
                    seq![config_volume]
                }
            }
        }),
        containers: seq![
            ContainerView {
                name: new_strlit("fluent-bit")@,
                image: Some(fb.spec.image),
                image_pull_policy: if fb.spec.image_pull_policy.is_Some() {
                        fb.spec.image_pull_policy
                    } else {
                        ContainerView::default().image_pull_policy
                    },
                env: if fb.spec.env_vars.is_Some() {
                        Some(make_env(fb) + fb.spec.env_vars.get_Some_0())
                    } else {
                        Some(make_env(fb))
                    },
                liveness_probe: if fb.spec.liveness_probe.is_Some() {
                        fb.spec.liveness_probe
                    } else {
                        ContainerView::default().liveness_probe
                    },
                readiness_probe: if fb.spec.readiness_probe.is_Some() {
                        fb.spec.readiness_probe
                    } else {
                        ContainerView::default().readiness_probe
                    },
                volume_mounts: Some({
                    let config_vm = VolumeMountView {
                        name: new_strlit("config")@,
                        read_only: Some(true),
                        mount_path: new_strlit("/fluent-bit/config")@,
                        ..VolumeMountView::default()
                    };
                    let varlibcontainers_vm = VolumeMountView {
                        name: new_strlit("varlibcontainers")@,
                        read_only: Some(true),
                        mount_path: if fb.spec.container_log_real_path.is_Some() { fb.spec.container_log_real_path.get_Some_0() } else { new_strlit("/containers")@ },
                        mount_propagation: fb.spec.internal_mount_propagation,
                        ..VolumeMountView::default()
                    };
                    let varlogs_vm = VolumeMountView {
                        name: new_strlit("varlogs")@,
                        read_only: Some(true),
                        mount_path: new_strlit("/var/log/")@,
                        mount_propagation: fb.spec.internal_mount_propagation,
                        ..VolumeMountView::default()
                    };
                    let systemd_vm = VolumeMountView {
                        name: new_strlit("systemd")@,
                        read_only: Some(true),
                        mount_path: new_strlit("/var/log/journal")@,
                        mount_propagation: fb.spec.internal_mount_propagation,
                        ..VolumeMountView::default()
                    };
                    if fb.spec.position_db.is_Some() {
                        let positions_vm = VolumeMountView {
                            name: new_strlit("positions")@,
                            mount_path: new_strlit("/fluent-bit/tail")@,
                            ..VolumeMountView::default()
                        };
                        if !fb.spec.disable_log_volumes && fb.spec.volume_mounts.is_Some() {
                            fb.spec.volume_mounts.get_Some_0().push(config_vm).push(varlibcontainers_vm).push(varlogs_vm)
                                .push(systemd_vm).push(positions_vm)
                        } else if !fb.spec.disable_log_volumes {
                            seq![config_vm, varlibcontainers_vm, varlogs_vm, systemd_vm, positions_vm]
                        } else if fb.spec.volume_mounts.is_Some() {
                            fb.spec.volume_mounts.get_Some_0().push(config_vm).push(positions_vm)
                        } else {
                            seq![config_vm, positions_vm]
                        }
                    } else {
                        if !fb.spec.disable_log_volumes && fb.spec.volume_mounts.is_Some() {
                            fb.spec.volume_mounts.get_Some_0().push(config_vm).push(varlibcontainers_vm).push(varlogs_vm).push(systemd_vm)
                        } else if !fb.spec.disable_log_volumes {
                            seq![config_vm, varlibcontainers_vm, varlogs_vm, systemd_vm]
                        } else if fb.spec.volume_mounts.is_Some() {
                            fb.spec.volume_mounts.get_Some_0().push(config_vm)
                        } else {
                            seq![config_vm]
                        }
                    }
                }),
                ports: {
                    let metrics_port = ContainerPortView::default()
                        .set_name(new_strlit("metrics")@)
                        .set_container_port({
                            let port = if fb.spec.metrics_port.is_Some() { fb.spec.metrics_port.get_Some_0() } else { 2020 };
                            port
                        });
                    if fb.spec.ports.is_Some() {
                        Some(fb.spec.ports.get_Some_0().push(metrics_port))
                    } else {
                        Some(seq![metrics_port])
                    }
                },
                resources: fb.spec.resources,
                args: if fb.spec.args.is_Some() {
                        fb.spec.args
                    } else {
                        ContainerView::default().args
                    },
                command: if fb.spec.command.is_Some() {
                        fb.spec.command
                    } else {
                        ContainerView::default().command
                    },
                security_context: if fb.spec.container_security_context.is_Some() {
                        fb.spec.container_security_context
                    } else {
                        ContainerView::default().security_context
                    },
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
        host_network: fb.spec.host_network,
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
