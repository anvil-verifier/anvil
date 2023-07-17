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
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RabbitmqReconcileState {
    pub reconcile_step: RabbitmqReconcileStep,
}

pub struct RabbitmqReconciler {}

impl Reconciler<RabbitmqClusterView, RabbitmqReconcileState> for RabbitmqReconciler {
    open spec fn reconcile_init_state() -> RabbitmqReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        rabbitmq: RabbitmqClusterView, resp_o: Option<APIResponse>, state: RabbitmqReconcileState
    ) -> (RabbitmqReconcileState, Option<APIRequest>) {
        reconcile_core(rabbitmq, resp_o, state)
    }

    open spec fn reconcile_done(state: RabbitmqReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: RabbitmqReconcileState) -> bool {
        reconcile_error(state)
    }
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

pub open spec fn reconcile_core(
    rabbitmq: RabbitmqClusterView, resp_o: Option<APIResponse>, state: RabbitmqReconcileState
) -> (RabbitmqReconcileState, Option<APIRequest>)
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let step = state.reconcile_step;
    match step{
        RabbitmqReconcileStep::Init => {
            let headless_service = make_headless_service(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
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
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
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
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
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
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
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
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: plugins_config_map.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreatePluginsConfigMap,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterCreatePluginsConfigMap => {
            let req_o = Option::Some(APIRequest::GetRequest(GetRequest{
                key: make_server_config_map_key(rabbitmq.object_ref())
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterGetServerConfigMap,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterGetServerConfigMap => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_GetResponse() {
                let config_map = make_server_config_map(rabbitmq);
                let get_config_resp = resp_o.get_Some_0().get_GetResponse_0().res;
                if get_config_resp.is_Ok() {
                    // update
                    if ConfigMapView::from_dynamic_object(get_config_resp.get_Ok_0()).is_Ok()
                    {
                        let found_config_map = ConfigMapView::from_dynamic_object(get_config_resp.get_Ok_0()).get_Ok_0();
                        let req_o = Option::Some(APIRequest::UpdateRequest(
                            UpdateRequest {
                                key: make_server_config_map_key(rabbitmq.object_ref()),
                                obj: found_config_map.set_data(config_map.data.get_Some_0()).to_dynamic_object(),
                            }
                        ));
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateServerConfigMap,
                            ..state
                        };
                        (state_prime, req_o)
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        let req_o = Option::None;
                        (state_prime, req_o)
                    }
                } else if get_config_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = Option::Some(APIRequest::CreateRequest(
                        CreateRequest {
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            obj: config_map.to_dynamic_object(),
                        }
                    ));
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateServerConfigMap,
                        ..state
                    };
                    (state_prime, req_o)
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    let req_o = Option::None;
                    (state_prime, req_o)
                }
            }else{
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                let req_o = Option::None;
                (state_prime, req_o)
            }

        },
        RabbitmqReconcileStep::AfterUpdateServerConfigMap => {
            let service_account = make_service_account(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: service_account.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateServiceAccount,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterCreateServerConfigMap => {
            let service_account = make_service_account(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: service_account.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateServiceAccount,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterCreateServiceAccount => {
            let role = make_role(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: role.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateRole,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterCreateRole => {
            let role_binding = make_role_binding(rabbitmq);
            let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: role_binding.to_dynamic_object(),
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateRoleBinding,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterCreateRoleBinding => {
            let req_o = Option::Some(APIRequest::GetRequest(GetRequest{
                key: ObjectRef {
                    kind: StatefulSetView::kind(),
                    name: rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@,
                    namespace: rabbitmq.metadata.namespace.get_Some_0(),
                }
            }));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterGetStatefulSet,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterGetStatefulSet => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_GetResponse() {
                let stateful_set = make_stateful_set(rabbitmq);
                let get_sts_resp = resp_o.get_Some_0().get_GetResponse_0().res;
                if get_sts_resp.is_Ok() {
                    // update
                    if StatefulSetView::from_dynamic_object(get_sts_resp.get_Ok_0()).is_Ok() {
                        let found_stateful_set = StatefulSetView::from_dynamic_object(get_sts_resp.get_Ok_0()).get_Ok_0();
                        if found_stateful_set.spec.is_Some()
                        && found_stateful_set.spec.get_Some_0().replicas.is_Some()
                        && found_stateful_set.spec.get_Some_0().replicas.get_Some_0() <= rabbitmq.spec.replicas
                        {
                            let req_o = Option::Some(APIRequest::UpdateRequest(
                                UpdateRequest {
                                    key: make_stateful_set_key(rabbitmq.object_ref()),
                                    obj: update_stateful_set(rabbitmq, found_stateful_set).to_dynamic_object(),
                                }
                            ));
                            let state_prime = RabbitmqReconcileState {
                                reconcile_step: RabbitmqReconcileStep::AfterUpdateStatefulSet,
                                ..state
                            };
                            (state_prime, req_o)
                        } else {
                            let state_prime = RabbitmqReconcileState {
                                reconcile_step: RabbitmqReconcileStep::Error,
                                ..state
                            };
                            let req_o = Option::None;
                            (state_prime, req_o)
                        }
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        let req_o = Option::None;
                        (state_prime, req_o)
                    }
                } else if get_sts_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = Option::Some(APIRequest::CreateRequest(
                        CreateRequest {
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            obj: stateful_set.to_dynamic_object(),
                        }
                    ));
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateStatefulSet,
                        ..state
                    };
                    (state_prime, req_o)
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    let req_o = Option::None;
                    (state_prime, req_o)
                }
            }else{
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                let req_o = Option::None;
                (state_prime, req_o)
            }

        },
        RabbitmqReconcileStep::AfterCreateStatefulSet => {
            let req_o = Option::None;
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterUpdateStatefulSet => {
            let req_o = Option::None;
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
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


    make_service(rabbitmq, rabbitmq.metadata.name.get_Some_0(), ports, true)
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

pub open spec fn make_server_config_map_name(rabbitmq_name: StringView) -> StringView {
    rabbitmq_name + new_strlit("-server-conf")@
}

pub open spec fn make_server_config_map_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: ConfigMapView::kind(),
        name: make_server_config_map_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn make_server_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ConfigMapView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_server_config_map_name(rabbitmq.metadata.name.get_Some_0()))
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_labels(Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()))
        )
        .set_data(Map::empty()
            .insert(new_strlit("operatorDefaults.conf")@, default_rbmq_config(rabbitmq))
            .insert(new_strlit("userDefinedConfiguration.conf")@,
            {
                if rabbitmq.spec.rabbitmq_config.is_Some()
                && rabbitmq.spec.rabbitmq_config.get_Some_0().additional_config.is_Some()
                {   // check if there are rabbitmq-related customized configurations
                    new_strlit("total_memory_available_override_value = 1717986919\n")@ + rabbitmq.spec.rabbitmq_config.get_Some_0().additional_config.get_Some_0()
                } else {
                    new_strlit("total_memory_available_override_value = 1717986919\n")@
                }
            })
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
    )@ + new_strlit("cluster_formation.target_cluster_size_hint = ")@ + int_to_string_view(rabbitmq.spec.replicas) + new_strlit("\n")@
    + new_strlit("cluster_name = ")@ + name + new_strlit("\n")@
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
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-peer-discovery")@)
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
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-peer-discovery")@)
        ).set_subjects(seq![SubjectView::default()
            .set_kind(new_strlit("ServiceAccount")@)
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
        ])
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

pub open spec fn make_stateful_set_name(rabbitmq_name: StringView) -> StringView {
    rabbitmq_name + new_strlit("-server")@
}

pub open spec fn update_stateful_set(rabbitmq: RabbitmqClusterView, found_stateful_set: StatefulSetView) -> StatefulSetView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    found_stateful_set.set_spec(make_stateful_set(rabbitmq).spec.get_Some_0())
}

pub open spec fn make_stateful_set(rabbitmq: RabbitmqClusterView) -> StatefulSetView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let name = rabbitmq.metadata.name.get_Some_0();
    let sts_name = make_stateful_set_name(name);
    let namespace = rabbitmq.metadata.namespace.get_Some_0();

    let labels = Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0());
    let metadata = ObjectMetaView::default()
        .set_name(sts_name)
        .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
        .set_labels(labels);

    let spec = StatefulSetSpecView::default()
        .set_replicas(rabbitmq.spec.replicas)
        .set_service_name(name + new_strlit("-nodes")@)
        .set_selector(LabelSelectorView::default().set_match_labels(labels))
        .set_template(PodTemplateSpecView::default()
            .set_metadata(ObjectMetaView::default()
                .set_labels(
                    Map::empty()
                        .insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0())
                )
            )
            .set_spec(make_rabbitmq_pod_spec(rabbitmq))
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
        ])
        .set_pod_management_policy(new_strlit("Parallel")@);

    StatefulSetView::default().set_metadata(metadata).set_spec(spec)
}


pub open spec fn make_rabbitmq_pod_spec(rabbitmq: RabbitmqClusterView) -> PodSpecView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
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
            .set_name(new_strlit("rabbitmq-erlang-cookie")@),
        VolumeView::default()
            .set_name(new_strlit("erlang-cookie-secret")@)
            .set_secret(SecretVolumeSourceView::default()
                .set_secret_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-erlang-cookie")@)
            ),
        VolumeView::default()
            .set_name(new_strlit("rabbitmq-plugins")@),
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

    PodSpecView::default()
        .set_service_account_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@)
        .set_init_containers(seq![
            ContainerView::default()
                .set_name(new_strlit("setup-container")@)
                .set_image(new_strlit("rabbitmq:3.11.10-management")@)
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
                        .set_mount_path(new_strlit("/etc/pod-info/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-confd")@)
                        .set_mount_path(new_strlit("/tmp/default_user.conf")@)
                        .set_sub_path(new_strlit("default_user.conf")@),
                ])
        ])
        .set_containers(seq![
            ContainerView::default()
                .set_name(new_strlit("rabbitmq")@)
                .set_image(new_strlit("rabbitmq:3.11.10-management")@)
                .set_volume_mounts(seq![
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
                ])
                .set_ports(seq![
                    ContainerPortView::default().set_name(new_strlit("epmd")@).set_container_port(4369),
                    ContainerPortView::default().set_name(new_strlit("amqp")@).set_container_port(5672),
                    ContainerPortView::default().set_name(new_strlit("management")@).set_container_port(15672),
                ])
        ])
        .set_volumes(volumes)
}

}
