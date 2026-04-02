// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::{
    container::*, volume::*, resource_requirements::*,
};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::model::{reconciler::*, install::rabbitmq_controller_model, resource::*};
use crate::rabbitmq_controller::trusted::{spec_types::*, step::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::int_to_string_view;
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::vstatefulset_controller::trusted::liveness_theorem as vsts_liveness_theorem;

use vstd::prelude::*;

use super::rely_guarantee::rmq_rely;
use super::spec_types::RabbitmqClusterView;

verus! {

pub open spec fn rmq_composed_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| composed_current_state_matches(vrs))
}

pub open spec fn rmq_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| current_state_matches(vrs))
}

pub open spec fn rmq_eventually_stable_reconciliation_per_cr(rmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation_per_cr(rmq, |rmq| current_state_matches(rmq))
}

pub open spec fn current_state_matches(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |sub_resource: SubResource| #[trigger] resource_state_matches(sub_resource, rabbitmq)(s)
    }
}

pub open spec fn composed_current_state_matches(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |ord: nat| ord < rabbitmq.spec.replicas ==> {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] vsts_liveness_theorem::pod_name(rabbitmq.metadata.name->0, ord),
                namespace: rabbitmq.metadata.namespace->0
            };
            let obj = s.resources()[key];
            &&& s.resources().contains_key(key)
            // spec is updated
            &&& PodView::unmarshal(obj) is Ok
            &&& pod_spec_matches_rmq(rabbitmq, PodView::unmarshal(obj)->Ok_0)
        }
    }
}

pub open spec fn pod_spec_matches_rmq(rabbitmq: RabbitmqClusterView, pod: PodView) -> bool {
    // TODO: define pod spec matching for composed RMQ liveness
    // Needs to compare pod spec against the VSTS template spec derived from rabbitmq
    &&& pod.spec is Some
    &&& pod.spec->0.without_volumes().without_hostname().without_subdomain()
        == make_rabbitmq_pod_spec(rabbitmq).without_volumes().without_hostname().without_subdomain()
}

pub open spec fn resource_state_matches(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |state: ClusterState| {
        let resources = state.resources();
        // shared by all objects
        &&& match sub_resource {
            SubResource::HeadlessService => {
                let key = make_headless_service_key(rabbitmq);
                let obj = resources[key];
                let made_spec = make_headless_service(rabbitmq).spec->0;
                let spec = ServiceView::unmarshal(obj)->Ok_0.spec->0;
                &&& resources.contains_key(key)
                &&& ServiceView::unmarshal(obj) is Ok
                &&& ServiceView::unmarshal(obj)->Ok_0.spec is Some
                &&& made_spec.without_cluster_ip() == spec.without_cluster_ip()
                &&& obj.metadata.labels == make_headless_service(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_headless_service(rabbitmq).metadata.annotations
                &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.deletion_timestamp is None
            },
            SubResource::Service => {
                let key = make_main_service_key(rabbitmq);
                let obj = resources[key];
                let made_spec = make_main_service(rabbitmq).spec->0;
                let spec = ServiceView::unmarshal(obj)->Ok_0.spec->0;
                &&& resources.contains_key(key)
                &&& ServiceView::unmarshal(obj) is Ok
                &&& ServiceView::unmarshal(obj)->Ok_0.spec is Some
                &&& made_spec.without_cluster_ip() == spec.without_cluster_ip()
                &&& obj.metadata.labels == make_main_service(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_main_service(rabbitmq).metadata.annotations
                &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.deletion_timestamp is None
            },
            SubResource::ErlangCookieSecret => {
                let key = make_erlang_secret_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& SecretView::unmarshal(obj) is Ok
                &&& obj.metadata.labels == make_erlang_secret(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_erlang_secret(rabbitmq).metadata.annotations
                &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.deletion_timestamp is None
            },
            SubResource::DefaultUserSecret => {
                let key = make_default_user_secret_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& SecretView::unmarshal(obj) is Ok
                &&& SecretView::unmarshal(obj)->Ok_0.data == make_default_user_secret(rabbitmq).data
                &&& obj.metadata.labels == make_default_user_secret(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_default_user_secret(rabbitmq).metadata.annotations
                &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.deletion_timestamp is None
            },
            SubResource::PluginsConfigMap => {
                let key = make_plugins_config_map_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& ConfigMapView::unmarshal(obj) is Ok
                &&& ConfigMapView::unmarshal(obj)->Ok_0.data == make_plugins_config_map(rabbitmq).data
                &&& obj.metadata.labels == make_plugins_config_map(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_plugins_config_map(rabbitmq).metadata.annotations
                &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.deletion_timestamp is None
            },
            SubResource::ServerConfigMap => {
                let key = make_server_config_map_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& ConfigMapView::unmarshal(obj) is Ok
                &&& ConfigMapView::unmarshal(obj)->Ok_0.data == make_server_config_map(rabbitmq).data
                &&& obj.spec == ConfigMapView::marshal_spec(make_server_config_map(rabbitmq).data)
                &&& obj.metadata.labels == make_server_config_map(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_server_config_map(rabbitmq).metadata.annotations
                &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.deletion_timestamp is None
            },
            SubResource::ServiceAccount => {
                let key = make_service_account_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& ServiceAccountView::unmarshal(obj) is Ok
                &&& obj.metadata.labels == make_service_account(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_service_account(rabbitmq).metadata.annotations
                &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.deletion_timestamp is None
            },
            SubResource::Role => {
                let key = make_role_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& RoleView::unmarshal(obj) is Ok
                &&& RoleView::unmarshal(obj)->Ok_0.policy_rules == make_role(rabbitmq).policy_rules
                &&& obj.metadata.labels == make_role(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_role(rabbitmq).metadata.annotations
                &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.deletion_timestamp is None
            },
            SubResource::RoleBinding => {
                let key = make_role_binding_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& RoleBindingView::unmarshal(obj) is Ok
                &&& RoleBindingView::unmarshal(obj)->Ok_0.subjects == make_role_binding(rabbitmq).subjects
                &&& obj.metadata.labels == make_role_binding(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_role_binding(rabbitmq).metadata.annotations
                &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.deletion_timestamp is None
            },
            SubResource::VStatefulSetView => {
                let key = make_stateful_set_key(rabbitmq);
                let obj = resources[key];
                let cm_key = make_server_config_map_key(rabbitmq);
                let cm_obj = resources[cm_key];
                let made_sts = make_stateful_set(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version->0));
                let etcd_sts = VStatefulSetView::unmarshal(obj)->Ok_0;
                &&& resources.contains_key(key)
                &&& resources.contains_key(cm_key)
                &&& cm_obj.metadata.resource_version is Some
                &&& VStatefulSetView::unmarshal(obj) is Ok
                &&& obj.metadata.labels == made_sts.metadata.labels
                &&& obj.metadata.annotations == made_sts.metadata.annotations
                &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.deletion_timestamp is None
                &&& etcd_sts.spec.replicas == Some(rabbitmq.spec.replicas)
                &&& etcd_sts.spec.template == made_sts.spec.template
                &&& etcd_sts.spec.persistent_volume_claim_retention_policy == rabbitmq.spec.persistent_volume_claim_retention_policy
                &&& Cluster::desired_state_is(etcd_sts)(state)
            },
        }
    }
}

pub open spec fn rmq_eventually_stable_cm_rv(spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rv: ResourceVersion) -> bool {
    spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(
        always(lift_state(config_map_rv_match(rabbitmq, rv)))
    ))
}

pub open spec fn config_map_rv_match(rabbitmq: RabbitmqClusterView, rv: ResourceVersion) -> StatePred<ClusterState> {
    |state: ClusterState| {
        let key = make_server_config_map_key(rabbitmq);
        let resources = state.resources();
        let obj = resources[key];
        &&& obj.metadata.resource_version is Some
        &&& obj.metadata.resource_version->0 == rv
    }
}

pub open spec fn make_rabbitmq_pod_spec(rabbitmq: RabbitmqClusterView) -> PodSpecView {
    let volumes = seq![
        VolumeView::default()
            .with_name("plugins-conf"@)
            .with_config_map(ConfigMapVolumeSourceView::default()
                .with_name(RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + rabbitmq.metadata.name->0 + "-plugins-conf"@)
            ),
        VolumeView::default()
            .with_name("rabbitmq-confd"@)
            .with_projected(ProjectedVolumeSourceView::default()
                .with_sources(seq![
                    VolumeProjectionView::default()
                        .with_config_map(ConfigMapProjectionView::default()
                            .with_name(RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + rabbitmq.metadata.name->0 + "-server-conf"@)
                            .with_items(seq![
                                KeyToPathView::default()
                                    .with_key("operatorDefaults.conf"@)
                                    .with_path("operatorDefaults.conf"@),
                                KeyToPathView::default()
                                    .with_key("userDefinedConfiguration.conf"@)
                                    .with_path("userDefinedConfiguration.conf"@),
                            ])
                        ),
                    VolumeProjectionView::default()
                        .with_secret(SecretProjectionView::default()
                            .with_name(RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + rabbitmq.metadata.name->0 + "-default-user"@)
                            .with_items(seq![
                                KeyToPathView::default()
                                    .with_key("default_user.conf"@)
                                    .with_path("default_user.conf"@),
                            ])
                        ),
                ])
            ),
        VolumeView::default()
            .with_name("rabbitmq-erlang-cookie"@)
            .with_empty_dir(EmptyDirVolumeSourceView::default()),
        VolumeView::default()
            .with_name("erlang-cookie-secret"@)
            .with_secret(SecretVolumeSourceView::default()
                .with_secret_name(RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + rabbitmq.metadata.name->0 + "-erlang-cookie"@)
            ),
        VolumeView::default()
            .with_name("rabbitmq-plugins"@)
            .with_empty_dir(EmptyDirVolumeSourceView::default()),
        VolumeView::default()
            .with_name("pod-info"@)
            .with_downward_api(DownwardAPIVolumeSourceView::default()
                .with_items(seq![
                    DownwardAPIVolumeFileView::default()
                        .with_path("skipPreStopChecks"@)
                        .with_field_ref(ObjectFieldSelectorView::default()
                            .with_field_path("metadata.labels['skipPreStopChecks']"@)
                        ),
                ])
            ),
    ];

    PodSpecView {
        service_account_name: Some(RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + rabbitmq.metadata.name->0 + "-server"@),
        init_containers: Some(
            seq![
                ContainerView::default()
                .with_name("setup-container"@)
                .with_image(rabbitmq.spec.image)
                .with_command(seq![
                        "sh"@,
                        "-c"@,
                        "cp /tmp/erlang-cookie-secret/.erlang.cookie /var/lib/rabbitmq/.erlang.cookie && chmod 600 /var/lib/rabbitmq/.erlang.cookie ; cp /tmp/rabbitmq-plugins/enabled_plugins /operator/enabled_plugins ; echo '[default]' > /var/lib/rabbitmq/.rabbitmqadmin.conf && sed -e 's/default_user/username/' -e 's/default_pass/password/' /tmp/default_user.conf >> /var/lib/rabbitmq/.rabbitmqadmin.conf && chmod 600 /var/lib/rabbitmq/.rabbitmqadmin.conf ; sleep 30"@
                ])
                .with_resources(
                    ResourceRequirementsView {
                        limits: Some(Map::empty().insert("cpu"@, "100m"@).insert("memory"@, "500Mi"@)),
                        requests: Some(Map::empty().insert("cpu"@, "100m"@).insert("memory"@, "500Mi"@)),
                    }
                )
                .with_volume_mounts(seq![
                    VolumeMountView::default()
                        .with_name("plugins-conf"@)
                        .with_mount_path("/tmp/rabbitmq-plugins/"@),
                    VolumeMountView::default()
                        .with_name("rabbitmq-erlang-cookie"@)
                        .with_mount_path("/var/lib/rabbitmq/"@),
                    VolumeMountView::default()
                        .with_name("erlang-cookie-secret"@)
                        .with_mount_path("/tmp/erlang-cookie-secret/"@),
                    VolumeMountView::default()
                        .with_name("rabbitmq-plugins"@)
                        .with_mount_path("/operator"@),
                    VolumeMountView::default()
                        .with_name("persistence"@)
                        .with_mount_path("/var/lib/rabbitmq/mnesia/"@),
                    VolumeMountView::default()
                        .with_name("rabbitmq-confd"@)
                        .with_mount_path("/tmp/default_user.conf"@)
                        .with_sub_path("default_user.conf"@),
                ])
            ]
        ),
        containers: seq![
            ContainerView {
                name: "rabbitmq"@,
                image: Some(rabbitmq.spec.image),
                lifecycle: Some(LifecycleView::default()
                    .with_pre_stop(LifecycleHandlerView::default()
                        .with_exec(
                            ExecActionView::default()
                                .with_command(seq!["/bin/bash"@, "-c"@,
                                    "if [ ! -z \"$(cat /etc/pod-info/skipPreStopChecks)\" ]; then exit 0; fi; \
                                    rabbitmq-upgrade await_online_quorum_plus_one -t 604800; \
                                    rabbitmq-upgrade await_online_synchronized_mirror -t 604800; \
                                    rabbitmq-upgrade drain -t 604800"@
                                ])
                        )
                    )
                ),
                env: Some(make_env_vars(rabbitmq)),
                volume_mounts: Some({
                    let volume_mounts = seq![
                        VolumeMountView::default()
                            .with_name("rabbitmq-erlang-cookie"@)
                            .with_mount_path("/var/lib/rabbitmq/"@),
                        VolumeMountView::default()
                            .with_name("persistence"@)
                            .with_mount_path("/var/lib/rabbitmq/mnesia/"@),
                        VolumeMountView::default()
                            .with_name("rabbitmq-plugins"@)
                            .with_mount_path("/operator"@),
                        VolumeMountView::default()
                            .with_name("rabbitmq-confd"@)
                            .with_mount_path("/etc/rabbitmq/conf.d/10-operatorDefaults.conf"@)
                            .with_sub_path("operatorDefaults.conf"@),
                        VolumeMountView::default()
                            .with_name("rabbitmq-confd"@)
                            .with_mount_path("/etc/rabbitmq/conf.d/90-userDefinedConfiguration.conf"@)
                            .with_sub_path("userDefinedConfiguration.conf"@),
                        VolumeMountView::default()
                            .with_name("pod-info"@)
                            .with_mount_path("/etc/pod-info/"@),
                        VolumeMountView::default()
                            .with_name("rabbitmq-confd"@)
                            .with_mount_path("/etc/rabbitmq/conf.d/11-default_user.conf"@)
                            .with_sub_path("default_user.conf"@),
                    ];
                    if rabbitmq.spec.rabbitmq_config is Some && rabbitmq.spec.rabbitmq_config->0.advanced_config is Some
                    && rabbitmq.spec.rabbitmq_config->0.advanced_config->0 != ""@
                    && rabbitmq.spec.rabbitmq_config->0.env_config is Some
                    && rabbitmq.spec.rabbitmq_config->0.env_config->0 != ""@ {
                        volume_mounts.push(
                            VolumeMountView::default()
                                .with_name("server-conf"@)
                                .with_mount_path("/etc/rabbitmq/rabbitmq-env.conf"@)
                                .with_sub_path("rabbitmq-env.conf"@)
                            ).push(
                            VolumeMountView::default()
                                .with_name("server-conf"@)
                                .with_mount_path("/etc/rabbitmq/advanced.config"@)
                                .with_sub_path("advanced.config"@)
                            )
                    } else if rabbitmq.spec.rabbitmq_config is Some && rabbitmq.spec.rabbitmq_config->0.advanced_config is Some
                    && rabbitmq.spec.rabbitmq_config->0.advanced_config->0 != ""@ {
                        volume_mounts.push(
                            VolumeMountView::default()
                                .with_name("server-conf"@)
                                .with_mount_path("/etc/rabbitmq/advanced.config"@)
                                .with_sub_path("advanced.config"@),
                        )
                    } else if rabbitmq.spec.rabbitmq_config is Some && rabbitmq.spec.rabbitmq_config->0.env_config is Some
                    && rabbitmq.spec.rabbitmq_config->0.env_config->0 != ""@ {
                        volume_mounts.push(
                            VolumeMountView::default()
                                .with_name("server-conf"@)
                                .with_mount_path("/etc/rabbitmq/rabbitmq-env.conf"@)
                                .with_sub_path("rabbitmq-env.conf"@),
                        )
                    } else {
                        volume_mounts
                    }
                }),
                ports: Some(seq![
                    ContainerPortView::default().with_name("epmd"@).with_container_port(4369),
                    ContainerPortView::default().with_name("amqp"@).with_container_port(5672),
                    ContainerPortView::default().with_name("management"@).with_container_port(15672),
                ]),
                readiness_probe: Some(
                    ProbeView::default()
                        .with_failure_threshold(3)
                        .with_initial_delay_seconds(10)
                        .with_period_seconds(10)
                        .with_success_threshold(1)
                        .with_timeout_seconds(5)
                        .with_tcp_socket(TCPSocketActionView::default().with_port(5672))
                ),
                resources: rabbitmq.spec.resources,
                ..ContainerView::default()
            }
        ],
        volumes: Some({
            if rabbitmq.spec.persistence.storage == "0Gi"@ {
                volumes.push(VolumeView::default().with_name("persistence"@).with_empty_dir(EmptyDirVolumeSourceView::default()))
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

}
