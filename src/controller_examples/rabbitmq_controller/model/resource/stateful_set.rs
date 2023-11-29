// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::resource::config_map::make_server_config_map_key;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct StatefulSetBuilder {}

impl ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState> for StatefulSetBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_stateful_set_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
        if state.latest_config_map_rv_opt.is_Some() {
            Ok(make_stateful_set(rabbitmq, state.latest_config_map_rv_opt.get_Some_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let sts = StatefulSetView::unmarshal(obj);
        let found_sts = sts.get_Ok_0();
        if sts.is_Ok() && found_sts.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
        && state.latest_config_map_rv_opt.is_Some() && found_sts.spec.is_Some() {
            Ok(update_stateful_set(rabbitmq, found_sts, state.latest_config_map_rv_opt.get_Some_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let sts = StatefulSetView::unmarshal(obj);
        if sts.is_Ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let sts = StatefulSetView::unmarshal(obj);
        if sts.is_Ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_stateful_set_key(rabbitmq: RabbitmqClusterView) -> ObjectRef {
    ObjectRef {
        kind: StatefulSetView::kind(),
        name: make_stateful_set_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn make_stateful_set_name(rabbitmq: RabbitmqClusterView) -> StringView { rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@ }

pub open spec fn sts_restart_annotation() -> StringView { new_strlit("anvil.dev/lastRestartAt")@ }

pub open spec fn update_stateful_set(rabbitmq: RabbitmqClusterView, found_stateful_set: StatefulSetView, config_map_rv: StringView) -> StatefulSetView {
    let made_spec = make_stateful_set(rabbitmq, config_map_rv).spec.get_Some_0();
    StatefulSetView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: make_stateful_set(rabbitmq, config_map_rv).metadata.labels,
            annotations: make_stateful_set(rabbitmq, config_map_rv).metadata.annotations,
            ..found_stateful_set.metadata
        },
        spec: Some(StatefulSetSpecView {
            replicas: made_spec.replicas,
            template: made_spec.template,
            persistent_volume_claim_retention_policy: made_spec.persistent_volume_claim_retention_policy,
            ..found_stateful_set.spec.get_Some_0()
        }),
        ..found_stateful_set
    }
}

pub open spec fn make_stateful_set(rabbitmq: RabbitmqClusterView, config_map_rv: StringView) -> StatefulSetView {
    let name = rabbitmq.metadata.name.get_Some_0();
    let sts_name = make_stateful_set_name(rabbitmq);
    let namespace = rabbitmq.metadata.namespace.get_Some_0();

    let labels = Map::empty().insert(new_strlit("app")@, name);
    let metadata = ObjectMetaView::default()
        .set_name(sts_name)
        .set_namespace(namespace)
        .set_owner_references(make_owner_references(rabbitmq))
        .set_labels(make_labels(rabbitmq))
        .set_annotations(rabbitmq.spec.annotations);

    let spec = StatefulSetSpecView {
        replicas: Some(rabbitmq.spec.replicas),
        service_name: name + new_strlit("-nodes")@,
        selector: LabelSelectorView::default().set_match_labels(labels),
        template: PodTemplateSpecView::default()
                    .set_metadata(
                        ObjectMetaView::default().set_labels(
                            make_labels(rabbitmq)
                        ).set_annotations(
                            rabbitmq.spec.annotations.insert(sts_restart_annotation(), config_map_rv)
                        )
                    )
                    .set_spec(make_rabbitmq_pod_spec(rabbitmq)),
        volume_claim_templates: Some({
            if rabbitmq.spec.persistence.storage == new_strlit("0Gi")@ {
                seq![]
            } else {
                seq![
                    PersistentVolumeClaimView::default()
                        .set_metadata(ObjectMetaView::default()
                            .set_name(new_strlit("persistence")@)
                            .set_namespace(namespace)
                            .set_labels(labels)
                        )
                        .set_spec(PersistentVolumeClaimSpecView::default()
                            .set_access_modes(seq![new_strlit("ReadWriteOnce")@])
                            .set_resources(ResourceRequirementsView::default()
                                .set_requests(Map::empty()
                                    .insert(new_strlit("storage")@, rabbitmq.spec.persistence.storage)
                                )
                            )
                            .set_storage_class_name(rabbitmq.spec.persistence.storage_class_name)
                        )
                ]
            }
        }),
        pod_management_policy: Some(rabbitmq.spec.pod_management_policy),
        persistent_volume_claim_retention_policy: rabbitmq.spec.persistent_volume_claim_retention_policy,
        ..StatefulSetSpecView::default()

    };

    StatefulSetView::default().set_metadata(metadata).set_spec(spec)
}

pub open spec fn make_rabbitmq_pod_spec(rabbitmq: RabbitmqClusterView) -> PodSpecView {
    let volumes = seq![
        VolumeView::default()
            .set_name(new_strlit("plugins-conf")@)
            .set_config_map(ConfigMapVolumeSourceView::default()
                .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-plugins-conf")@)
            ),
        VolumeView::default()
            .set_name(new_strlit("rabbitmq-confd")@)
            .set_projected(ProjectedVolumeSourceView::default()
                .set_sources(seq![
                    VolumeProjectionView::default()
                        .set_config_map(ConfigMapProjectionView::default()
                            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server-conf")@)
                            .set_items(seq![
                                KeyToPathView::default()
                                    .set_key(new_strlit("operatorDefaults.conf")@)
                                    .set_path(new_strlit("operatorDefaults.conf")@),
                                KeyToPathView::default()
                                    .set_key(new_strlit("userDefinedConfiguration.conf")@)
                                    .set_path(new_strlit("userDefinedConfiguration.conf")@),
                            ])
                        ),
                    VolumeProjectionView::default()
                        .set_secret(SecretProjectionView::default()
                            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-default-user")@)
                            .set_items(seq![
                                KeyToPathView::default()
                                    .set_key(new_strlit("default_user.conf")@)
                                    .set_path(new_strlit("default_user.conf")@),
                            ])
                        ),
                ])
            ),
        VolumeView::default()
            .set_name(new_strlit("rabbitmq-erlang-cookie")@)
            .set_empty_dir(EmptyDirVolumeSourceView::default()),
        VolumeView::default()
            .set_name(new_strlit("erlang-cookie-secret")@)
            .set_secret(SecretVolumeSourceView::default()
                .set_secret_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-erlang-cookie")@)
            ),
        VolumeView::default()
            .set_name(new_strlit("rabbitmq-plugins")@)
            .set_empty_dir(EmptyDirVolumeSourceView::default()),
        VolumeView::default()
            .set_name(new_strlit("pod-info")@)
            .set_downward_api(DownwardAPIVolumeSourceView::default()
                .set_items(seq![
                    DownwardAPIVolumeFileView::default()
                        .set_path(new_strlit("skipPreStopChecks")@)
                        .set_field_ref(ObjectFieldSelectorView::default()
                            .set_field_path(new_strlit("metadata.labels['skipPreStopChecks']")@)
                        ),
                ])
            ),
    ];

    PodSpecView {
        service_account_name: Some(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@),
        init_containers: Some(
            seq![
                ContainerView::default()
                .set_name(new_strlit("setup-container")@)
                .set_image(rabbitmq.spec.image)
                .set_command(seq![
                        new_strlit("sh")@,
                        new_strlit("-c")@,
                        new_strlit("cp /tmp/erlang-cookie-secret/.erlang.cookie /var/lib/rabbitmq/.erlang.cookie && chmod 600 /var/lib/rabbitmq/.erlang.cookie ; cp /tmp/rabbitmq-plugins/enabled_plugins /operator/enabled_plugins ; echo '[default]' > /var/lib/rabbitmq/.rabbitmqadmin.conf && sed -e 's/default_user/username/' -e 's/default_pass/password/' /tmp/default_user.conf >> /var/lib/rabbitmq/.rabbitmqadmin.conf && chmod 600 /var/lib/rabbitmq/.rabbitmqadmin.conf ; sleep 30")@
                ])
                .set_resources(
                    ResourceRequirementsView {
                        limits: Some(Map::empty().insert(new_strlit("cpu")@, new_strlit("100m")@).insert(new_strlit("memory")@, new_strlit("500Mi")@)),
                        requests: Some(Map::empty().insert(new_strlit("cpu")@, new_strlit("100m")@).insert(new_strlit("memory")@, new_strlit("500Mi")@)),
                    }
                )
                .set_volume_mounts(seq![
                    VolumeMountView::default()
                        .set_name(new_strlit("plugins-conf")@)
                        .set_mount_path(new_strlit("/tmp/rabbitmq-plugins/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-erlang-cookie")@)
                        .set_mount_path(new_strlit("/var/lib/rabbitmq/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("erlang-cookie-secret")@)
                        .set_mount_path(new_strlit("/tmp/erlang-cookie-secret/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-plugins")@)
                        .set_mount_path(new_strlit("/operator")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("persistence")@)
                        .set_mount_path(new_strlit("/var/lib/rabbitmq/mnesia/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-confd")@)
                        .set_mount_path(new_strlit("/tmp/default_user.conf")@)
                        .set_sub_path(new_strlit("default_user.conf")@),
                ])
            ]
        ),
        containers: seq![
            ContainerView {
                name: new_strlit("rabbitmq")@,
                image: Some(rabbitmq.spec.image),
                lifecycle: Some(LifecycleView::default()
                    .set_pre_stop(LifecycleHandlerView::default()
                        .set_exec(
                            ExecActionView::default()
                                .set_command(seq![new_strlit("/bin/bash")@, new_strlit("-c")@,
                                    new_strlit("if [ ! -z \"$(cat /etc/pod-info/skipPreStopChecks)\" ]; then exit 0; fi; \
                                    rabbitmq-upgrade await_online_quorum_plus_one -t 604800; \
                                    rabbitmq-upgrade await_online_synchronized_mirror -t 604800; \
                                    rabbitmq-upgrade drain -t 604800")@
                                ])
                        )
                    )
                ),
                env: Some(make_env_vars(rabbitmq)),
                volume_mounts: Some({
                    let volume_mounts = seq![
                        VolumeMountView::default()
                            .set_name(new_strlit("rabbitmq-erlang-cookie")@)
                            .set_mount_path(new_strlit("/var/lib/rabbitmq/")@),
                        VolumeMountView::default()
                            .set_name(new_strlit("persistence")@)
                            .set_mount_path(new_strlit("/var/lib/rabbitmq/mnesia/")@),
                        VolumeMountView::default()
                            .set_name(new_strlit("rabbitmq-plugins")@)
                            .set_mount_path(new_strlit("/operator")@),
                        VolumeMountView::default()
                            .set_name(new_strlit("rabbitmq-confd")@)
                            .set_mount_path(new_strlit("/etc/rabbitmq/conf.d/10-operatorDefaults.conf")@)
                            .set_sub_path(new_strlit("operatorDefaults.conf")@),
                        VolumeMountView::default()
                            .set_name(new_strlit("rabbitmq-confd")@)
                            .set_mount_path(new_strlit("/etc/rabbitmq/conf.d/90-userDefinedConfiguration.conf")@)
                            .set_sub_path(new_strlit("userDefinedConfiguration.conf")@),
                        VolumeMountView::default()
                            .set_name(new_strlit("pod-info")@)
                            .set_mount_path(new_strlit("/etc/pod-info/")@),
                        VolumeMountView::default()
                            .set_name(new_strlit("rabbitmq-confd")@)
                            .set_mount_path(new_strlit("/etc/rabbitmq/conf.d/11-default_user.conf")@)
                            .set_sub_path(new_strlit("default_user.conf")@),
                    ];
                    if rabbitmq.spec.rabbitmq_config.is_Some() && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.is_Some()
                    && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.get_Some_0() != new_strlit("")@
                    && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.is_Some()
                    && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.get_Some_0() != new_strlit("")@ {
                        volume_mounts.push(
                            VolumeMountView::default()
                                .set_name(new_strlit("server-conf")@)
                                .set_mount_path(new_strlit("/etc/rabbitmq/rabbitmq-env.conf")@)
                                .set_sub_path(new_strlit("rabbitmq-env.conf")@)
                            ).push(
                            VolumeMountView::default()
                                .set_name(new_strlit("server-conf")@)
                                .set_mount_path(new_strlit("/etc/rabbitmq/advanced.config")@)
                                .set_sub_path(new_strlit("advanced.config")@)
                            )
                    } else if rabbitmq.spec.rabbitmq_config.is_Some() && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.is_Some()
                    && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.get_Some_0() != new_strlit("")@ {
                        volume_mounts.push(
                            VolumeMountView::default()
                                .set_name(new_strlit("server-conf")@)
                                .set_mount_path(new_strlit("/etc/rabbitmq/advanced.config")@)
                                .set_sub_path(new_strlit("advanced.config")@),
                        )
                    } else if rabbitmq.spec.rabbitmq_config.is_Some() && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.is_Some()
                    && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.get_Some_0() != new_strlit("")@ {
                        volume_mounts.push(
                            VolumeMountView::default()
                                .set_name(new_strlit("server-conf")@)
                                .set_mount_path(new_strlit("/etc/rabbitmq/rabbitmq-env.conf")@)
                                .set_sub_path(new_strlit("rabbitmq-env.conf")@),
                        )
                    } else {
                        volume_mounts
                    }
                }),
                ports: Some(seq![
                    ContainerPortView::default().set_name(new_strlit("epmd")@).set_container_port(4369),
                    ContainerPortView::default().set_name(new_strlit("amqp")@).set_container_port(5672),
                    ContainerPortView::default().set_name(new_strlit("management")@).set_container_port(15672),
                ]),
                readiness_probe: Some(
                    ProbeView::default()
                        .set_failure_threshold(3)
                        .set_initial_delay_seconds(10)
                        .set_period_seconds(10)
                        .set_success_threshold(1)
                        .set_timeout_seconds(5)
                        .set_tcp_socket(TCPSocketActionView::default().set_port(5672))
                ),
                resources: rabbitmq.spec.resources,
                ..ContainerView::default()
            }
        ],
        volumes: Some({
            if rabbitmq.spec.persistence.storage == new_strlit("0Gi")@ {
                volumes.push(VolumeView::default().set_name(new_strlit("persistence")@).set_empty_dir(EmptyDirVolumeSourceView::default()))
            } else {
                volumes
            }
        }),
        affinity: rabbitmq.spec.affinity,
        tolerations: rabbitmq.spec.tolerations,
        // TODO: do not hardcode this value
        termination_grace_period_seconds: Some(604800),
        ..PodSpecView::default()
    }
}

pub open spec fn make_env_vars(rabbitmq: RabbitmqClusterView) -> Seq<EnvVarView> {
    seq![
        EnvVarView {
            name: new_strlit("MY_POD_NAME")@,
            value_from: Some(EnvVarSourceView {
                field_ref: Some(ObjectFieldSelectorView{
                    api_version: Some(new_strlit("v1")@),
                    field_path: new_strlit("metadata.name")@,
                    ..ObjectFieldSelectorView::default()
                }),
                ..EnvVarSourceView::default()
            }),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("MY_POD_NAMESPACE")@,
            value_from: Some(EnvVarSourceView {
                field_ref: Some(ObjectFieldSelectorView{
                    api_version: Some(new_strlit("v1")@),
                    field_path: new_strlit("metadata.namespace")@,
                    ..ObjectFieldSelectorView::default()
                }),
                ..EnvVarSourceView::default()
            }),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("K8S_SERVICE_NAME")@,
            value: Some(rabbitmq.metadata.name.get_Some_0() + new_strlit("-nodes")@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("RABBITMQ_ENABLED_PLUGINS_FILE")@,
            value: Some(new_strlit("/operator/enabled_plugins")@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("RABBITMQ_USE_LONGNAME")@,
            value: Some(new_strlit("true")@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("RABBITMQ_NODENAME")@,
            value: Some(new_strlit("rabbit@$(MY_POD_NAME).$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)")@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("K8S_HOSTNAME_SUFFIX")@,
            value: Some(new_strlit(".$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)")@),
            ..EnvVarView::default()
        },
    ]
}

}
