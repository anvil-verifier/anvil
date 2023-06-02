// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, label_selector::*, object_meta::*,
    persistent_volume_claim::*, pod::*, pod_template_spec::*, resource::*, role::*,
    role_binding::*, secret::*, service::*, service_account::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::rabbitmqcluster::*;
use crate::reconciler::spec::*;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RabbitmqReconcileState {
    pub reconcile_step: RabbitmqReconcileStep,
}

pub open spec fn reconcile_init_state() -> RabbitmqReconcileState {
    RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Init,
    }
}

pub open spec fn reconcile_done(state: RabbitmqReconcileState) -> bool {
    match state.reconcile_step {
        RabbitmqReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: RabbitmqReconcileState) -> bool {
    match state.reconcile_step {
        RabbitmqReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(rabbitmq: RabbitmqClusterView, resp_o: Option<APIResponse>, state: RabbitmqReconcileState) -> (RabbitmqReconcileState, Option<APIRequest>)
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let step = state.reconcile_step;
    match step{
        RabbitmqReconcileStep::Init => {
            let headless_service = make_headless_service(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                obj: headless_service.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateHeadlessService,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterCreateHeadlessService => {
            let main_service = make_main_service(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                obj: main_service.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateService,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterCreateService => {
            let erlang_secret = make_erlang_secret(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                obj: erlang_secret.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateErlangCookieSecret,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterCreateErlangCookieSecret => {
            let default_user_secret = make_default_user_secret(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                obj: default_user_secret.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateDefaultUserSecret,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterCreateDefaultUserSecret => {
            let plugins_config_map = make_plugins_config_map(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                obj: plugins_config_map.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreatePluginsConfigMap,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterCreatePluginsConfigMap => {
            let server_config_map = make_server_config_map(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                obj: server_config_map.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateServerConfigMap,
                ..state
            };
            (state_prime, req_o)
        },
        _ => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = Option::None;
            (state_prime, req_o)
        }

    }
}


pub open spec fn reconcile_error_result(state: RabbitmqReconcileState) -> (RabbitmqReconcileState, Option<APIRequest>) {
    let state_prime = RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Error,
        ..state
    };
    let req_o = Option::None;
    (state_prime, req_o)
}


pub open spec fn make_headless_service(rabbitmq: RabbitmqClusterView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let mut ports = seq![
        ServicePortView::default().set_name(new_strlit("epmd")@).set_port(4369),
        ServicePortView::default().set_name(new_strlit("cluster-rpc")@).set_port(25672)
    ];

    make_service(rabbitmq, rabbitmq.metadata.name.get_Some_0() + new_strlit("-nodes")@, ports, false)
}

pub open spec fn make_main_service(rabbitmq: RabbitmqClusterView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let ports = seq![
        ServicePortView::default().set_name(new_strlit("amqp")@).set_port(5672).set_app_protocol(new_strlit("amqp")@),
        ServicePortView::default().set_name(new_strlit("management")@).set_port(15672).set_app_protocol(new_strlit("http")@),
    ];


    make_service(rabbitmq, rabbitmq.metadata.name.get_Some_0(), ports, false)
}

pub open spec fn make_service(
    rabbitmq: RabbitmqClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool
) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ServiceView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(name)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_labels(Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()))
        ).set_spec({
            let spec = ServiceSpecView::default()
                .set_ports(ports)
                .set_selector(Map::empty()
                    .insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0())
                ).set_publish_not_ready_addresses(true);
            if !cluster_ip {
                spec.set_cluster_ip(new_strlit("None")@)
            } else {
                spec
            }
        })
}


pub open spec fn make_erlang_secret(rabbitmq: RabbitmqClusterView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let cookie = random_encoded_string(24);
    let data = Map::empty()
        .insert(new_strlit(".erlang.cookie")@, cookie);


    make_secret(rabbitmq, rabbitmq.metadata.name.get_Some_0() + new_strlit("-erlang-cookie")@, data)
}

pub closed spec fn random_encoded_string(length: usize) -> StringView;

pub open spec fn make_default_user_secret(rabbitmq: RabbitmqClusterView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let data = Map::empty()
        .insert(new_strlit("username")@, new_strlit("user")@)
        .insert(new_strlit("password")@, new_strlit("changeme")@)
        .insert(new_strlit("type")@, new_strlit("rabbitmq")@)
        .insert(new_strlit("host")@,
            rabbitmq.metadata.name.get_Some_0() + new_strlit(".")@ + rabbitmq.metadata.namespace.get_Some_0() + new_strlit(".svc")@,
        )
        .insert(new_strlit("provider")@, new_strlit("rabbitmq")@)
        .insert(new_strlit("default_user.conf")@, new_strlit("default_user = user\ndefault_pass = changeme")@)
        .insert(new_strlit(".port")@, new_strlit("5672")@);


    make_secret(rabbitmq, rabbitmq.metadata.name.get_Some_0() + new_strlit("-default-user")@, data)
}



pub open spec fn make_secret(
    rabbitmq: RabbitmqClusterView, name: StringView, data: Map<StringView, StringView>
) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    SecretView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(name)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_labels(Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()))
        ).set_data(data)
}


pub open spec fn make_plugins_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ConfigMapView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-plugins-conf")@)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_labels(Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()))
        )
        .set_data(Map::empty()
            .insert(new_strlit("enabled_plugins")@, new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_management].")@)
        )
}

pub open spec fn make_server_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ConfigMapView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server-conf")@)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_labels(Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()))
        )
        .set_data(Map::empty()
            .insert(new_strlit("operatorDefaults.conf")@, default_rbmq_config(rabbitmq))
            .insert(new_strlit("userDefineConfiguration.conf")@, new_strlit("total_memory_available_override_value = 1717986919\n")@)
        )
}

pub open spec fn default_rbmq_config(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let name = rabbitmq.metadata.name.get_Some_0();

    new_strlit(
        "queue_master_locator = min-masters\n\
        disk_free_limit.absolute = 2GB\n\
        cluster_partition_handling = pause_minority\n\
        cluster_formation.peer_discovery_backend = rabbit_peer_discovery_k8s\n\
        cluster_formation.k8s.host = kubernetes.default\n\
        cluster_formation.k8s.address_type = hostname\n"
    )@ + new_strlit("cluster_formation.target_cluster_size_hint = {}\n")@ + int_to_string_view(rabbitmq.spec.replica) + new_strlit("cluster_name = {}\n")@ + name
}

pub open spec fn make_service_account(rabbitmq: RabbitmqClusterView) -> ServiceAccountView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ServiceAccountView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_labels(Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()))
        )

}



pub open spec fn make_role(rabbitmq: RabbitmqClusterView) -> RoleView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    RoleView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-peer-discorvery")@)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_labels(Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()))
        ).set_policy_rules(
            seq![
                PolicyRuleView::default().set_api_groups(seq![new_strlit("")@]).set_resources(seq![new_strlit("endpoints")@]).set_verbs(seq![new_strlit("get")@]),
                PolicyRuleView::default().set_api_groups(seq![new_strlit("")@]).set_resources(seq![new_strlit("events")@]).set_verbs(seq![new_strlit("create")@]),
            ]
        )

}


pub open spec fn make_role_binding(rabbitmq: RabbitmqClusterView) -> RoleBindingView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    RoleBindingView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_labels(Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()))
        ).set_role_ref(RoleRefView::default()
            .set_api_group(new_strlit("rbac.authorization.k8s.io")@)
            .set_kind(new_strlit("Role")@)
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-peer-discorvery")@)
        ).set_subjects(seq![SubjectView::default()
            .set_kind(new_strlit("ServiceAccount")@)
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
        ])
}


pub open spec fn make_stateful_set(rabbitmq: RabbitmqClusterView) -> StatefulSetView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let name = rabbitmq.metadata.name.get_Some_0();
    let sts_name = rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@;
    let namespace = rabbitmq.metadata.namespace.get_Some_0();

    let labels = Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0());
    let metadata = ObjectMetaView::default()
        .set_name(sts_name)
        .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
        .set_labels(labels);

    let spec = StatefulSetSpecView::default()
        .set_replicas(rabbitmq.spec.replica)
        .set_service_name(name + new_strlit("-nodes")@)
        .set_selector(LabelSelectorView::default().set_match_labels(labels))
        .set_template(PodTemplateSpecView::default()
            .set_metadata(ObjectMetaView::default()
                .set_labels(
                    Map::empty()
                        .insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0())
                )
            )
            // .set_spec(make_rabbitmq_pod_spec(rabbitmq))
        )
        .set_volume_claim_templates(seq![
            PersistentVolumeClaimView::default()
                .set_metadata(ObjectMetaView::default()
                    .set_name(new_strlit("persistence")@)
                    .set_namespace(namespace)
                    .set_labels(labels)
                )
                .set_spec(PersistentVolumeClaimSpecView::default()
                    .set_access_modes(seq![new_strlit("ReadWriteOnce")@])
                )
        ]);

    StatefulSetView::default().set_metadata(metadata).set_spec(spec)
}










}
