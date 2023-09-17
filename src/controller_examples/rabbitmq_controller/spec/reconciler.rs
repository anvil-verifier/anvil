// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, container::*, dynamic::*, label_selector::*,
    object_meta::*, persistent_volume_claim::*, pod::*, pod_template_spec::*, resource::*,
    resource_requirements::*, role::*, role_binding::*, secret::*, service::*, service_account::*,
    stateful_set::*, volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::rabbitmqcluster::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RabbitmqReconcileState {
    pub reconcile_step: RabbitmqReconcileStep,
    pub latest_config_map_rv_opt: Option<StringView>,
}

pub struct RabbitmqReconciler {}

impl Reconciler<RabbitmqClusterView, EmptyAPI> for RabbitmqReconciler {
    type T = RabbitmqReconcileState;

    open spec fn reconcile_init_state() -> RabbitmqReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        rabbitmq: RabbitmqClusterView, resp_o: Option<ResponseView<EmptyTypeView>>, state: RabbitmqReconcileState
    ) -> (RabbitmqReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(rabbitmq, resp_o, state)
    }

    open spec fn reconcile_done(state: RabbitmqReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: RabbitmqReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool {
        false // Don't expect anything from the user except the cr object
    }
}

pub open spec fn reconcile_init_state() -> RabbitmqReconcileState {
    RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Init,
        latest_config_map_rv_opt: None,
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
    rabbitmq: RabbitmqClusterView, resp_o: Option<ResponseView<EmptyTypeView>>, state: RabbitmqReconcileState
) -> (RabbitmqReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let step = state.reconcile_step;
    match step{
        RabbitmqReconcileStep::Init => {
            let headless_service = make_headless_service(rabbitmq);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: headless_service.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateHeadlessService,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterCreateHeadlessService => {
            let main_service = make_main_service(rabbitmq);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: main_service.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateService,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterCreateService => {
            let erlang_secret = make_erlang_secret(rabbitmq);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: erlang_secret.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateErlangCookieSecret,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterCreateErlangCookieSecret => {
            let default_user_secret = make_default_user_secret(rabbitmq);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: default_user_secret.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateDefaultUserSecret,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterCreateDefaultUserSecret => {
            let plugins_config_map = make_plugins_config_map(rabbitmq);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: plugins_config_map.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreatePluginsConfigMap,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterCreatePluginsConfigMap => {
            let req_o = APIRequest::GetRequest(GetRequest{
                key: make_server_config_map_key(rabbitmq.object_ref())
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterGetServerConfigMap,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterGetServerConfigMap => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let config_map = make_server_config_map(rabbitmq);
                let get_config_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_config_resp.is_Ok() {
                    // update
                    if ConfigMapView::from_dynamic_object(get_config_resp.get_Ok_0()).is_Ok()
                    {
                        let found_config_map = ConfigMapView::from_dynamic_object(get_config_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            key: make_server_config_map_key(rabbitmq.object_ref()),
                            obj: update_server_config_map(rabbitmq, found_config_map).to_dynamic_object(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateServerConfigMap,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_config_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: config_map.to_dynamic_object(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateServerConfigMap,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdateServerConfigMap => {
            let update_cm_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_cm = ConfigMapView::from_dynamic_object(update_cm_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_cm_resp.is_Ok() && latest_cm.is_Ok() && latest_cm.get_Ok_0().metadata.resource_version.is_Some() {
                let service_account = make_service_account(rabbitmq);
                let req_o = APIRequest::CreateRequest(CreateRequest{
                    namespace: rabbitmq.metadata.namespace.get_Some_0(),
                    obj: service_account.to_dynamic_object(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterCreateServiceAccount,
                    latest_config_map_rv_opt: Some(int_to_string_view(latest_cm.get_Ok_0().metadata.resource_version.get_Some_0())),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateServerConfigMap => {
            let create_cm_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_cm = ConfigMapView::from_dynamic_object(create_cm_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_cm_resp.is_Ok() && latest_cm.is_Ok() && latest_cm.get_Ok_0().metadata.resource_version.is_Some() {
                let service_account = make_service_account(rabbitmq);
                let req_o = APIRequest::CreateRequest(CreateRequest{
                    namespace: rabbitmq.metadata.namespace.get_Some_0(),
                    obj: service_account.to_dynamic_object(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterCreateServiceAccount,
                    latest_config_map_rv_opt: Some(int_to_string_view(latest_cm.get_Ok_0().metadata.resource_version.get_Some_0())),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateServiceAccount => {
            let role = make_role(rabbitmq);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: role.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateRole,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterCreateRole => {
            let role_binding = make_role_binding(rabbitmq);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                obj: role_binding.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateRoleBinding,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterCreateRoleBinding => {
            let req_o = APIRequest::GetRequest(GetRequest{
                key: make_stateful_set_key(rabbitmq.object_ref()),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterGetStatefulSet,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterGetStatefulSet => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse()
            && state.latest_config_map_rv_opt.is_Some() {
                let get_sts_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_sts_resp.is_Ok() {
                    // update
                    if StatefulSetView::from_dynamic_object(get_sts_resp.get_Ok_0()).is_Ok() {
                        let found_stateful_set = StatefulSetView::from_dynamic_object(get_sts_resp.get_Ok_0()).get_Ok_0();
                        if found_stateful_set.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref()) {
                            let req_o = APIRequest::UpdateRequest(UpdateRequest {
                                key: make_stateful_set_key(rabbitmq.object_ref()),
                                obj: update_stateful_set(
                                    rabbitmq, found_stateful_set,
                                    state.latest_config_map_rv_opt.get_Some_0()
                                ).to_dynamic_object(),
                            });
                            let state_prime = RabbitmqReconcileState {
                                reconcile_step: RabbitmqReconcileStep::AfterUpdateStatefulSet,
                                ..state
                            };
                            (state_prime, Some(RequestView::KRequest(req_o)))
                        } else {
                            let state_prime = RabbitmqReconcileState {
                                reconcile_step: RabbitmqReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_sts_resp.get_Err_0().is_ObjectNotFound() {
                    let stateful_set = make_stateful_set(rabbitmq, state.latest_config_map_rv_opt.get_Some_0());
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: stateful_set.to_dynamic_object(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateStatefulSet,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateStatefulSet => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            (state_prime, None)
        },
        RabbitmqReconcileStep::AfterUpdateStatefulSet => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            (state_prime, None)
        },
        _ => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: step,
                ..state
            };
            (state_prime, None)
        }
    }
}

pub open spec fn reconcile_error_result(state: RabbitmqReconcileState) -> (RabbitmqReconcileState, Option<APIRequest>) {
    let state_prime = RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Error,
        ..state
    };
    let req_o = None;
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
            .set_owner_references(seq![rabbitmq.controller_owner_ref()])
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
        .insert(new_strlit("port")@, new_strlit("5672")@);
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
            .set_owner_references(seq![rabbitmq.controller_owner_ref()])
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
            .set_owner_references(seq![rabbitmq.controller_owner_ref()])
            .set_labels(Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()))
        )
        .set_data(Map::empty()
            .insert(new_strlit("enabled_plugins")@, new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_management].")@)
        )
}

pub open spec fn update_server_config_map(rabbitmq: RabbitmqClusterView, found_config_map: ConfigMapView) -> ConfigMapView {
    let metadata = found_config_map.metadata.set_owner_references(seq![rabbitmq.controller_owner_ref()]).unset_finalizers();
    found_config_map.set_data(make_server_config_map(rabbitmq).data.get_Some_0()).set_metadata(metadata)
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
            .set_owner_references(seq![rabbitmq.controller_owner_ref()])
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
            .set_owner_references(seq![rabbitmq.controller_owner_ref()])
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
            .set_owner_references(seq![rabbitmq.controller_owner_ref()])
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
            .set_owner_references(seq![rabbitmq.controller_owner_ref()])
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

pub open spec fn update_stateful_set(
    rabbitmq: RabbitmqClusterView, found_stateful_set: StatefulSetView, config_map_rv: StringView
) -> StatefulSetView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let metadata = found_stateful_set.metadata.set_owner_references(seq![rabbitmq.controller_owner_ref()]).unset_finalizers();
    found_stateful_set.set_spec(make_stateful_set(rabbitmq, config_map_rv).spec.get_Some_0()).set_metadata(metadata)
}

pub open spec fn sts_restart_annotation() -> StringView {
    new_strlit("anvil.dev/lastRestartAt")@
}

pub open spec fn make_stateful_set(rabbitmq: RabbitmqClusterView, config_map_rv: StringView) -> StatefulSetView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let name = rabbitmq.metadata.name.get_Some_0();
    let sts_name = make_stateful_set_name(name);
    let namespace = rabbitmq.metadata.namespace.get_Some_0();

    let labels = Map::empty().insert(new_strlit("app")@, name);
    let metadata = ObjectMetaView::default()
        .set_name(sts_name)
        .set_namespace(namespace)
        .set_owner_references(seq![rabbitmq.controller_owner_ref()])
        .set_labels(labels);

    let spec = StatefulSetSpecView {
        replicas: Some(rabbitmq.spec.replicas),
        service_name: name + new_strlit("-nodes")@,
        selector: LabelSelectorView::default().set_match_labels(labels),
        template: PodTemplateSpecView::default()
                    .set_metadata(
                        ObjectMetaView::default().set_labels(
                            Map::empty()
                                .insert(new_strlit("app")@, name)
                        ).add_annotation(
                            sts_restart_annotation(), config_map_rv
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
                            .overwrite_storage_class_name(rabbitmq.spec.persistence.storage_class_name)
                        )
                ]
            }
        }),
        pod_management_policy: Some({
            if rabbitmq.spec.pod_management_policy.is_Some() {
                rabbitmq.spec.pod_management_policy.get_Some_0()
            } else {
                new_strlit("Parallel")@
            }
        }),
        persistent_volume_claim_retention_policy: rabbitmq.spec.persistent_volume_claim_retention_policy,
        ..StatefulSetSpecView::default()

    };

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

    PodSpecView {
        service_account_name: Some(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@),
        init_containers: Some(
            seq![
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
            ]
        ),
        containers: seq![
            ContainerView {
                name: new_strlit("rabbitmq")@,
                image: Some(new_strlit("rabbitmq:3.11.10-management")@),
                volume_mounts: Some(seq![
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
                ]),
                ports: Some(seq![
                    ContainerPortView::default().set_name(new_strlit("epmd")@).set_container_port(4369),
                    ContainerPortView::default().set_name(new_strlit("amqp")@).set_container_port(5672),
                    ContainerPortView::default().set_name(new_strlit("management")@).set_container_port(15672),
                ]),
                readiness_probe: Some(
                    ProbeView::default()
                        .set_failure_threshold(3)
                        .set_initial_delay_seconds(50)
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
                volumes.push(VolumeView::default().set_name(new_strlit("persistence")@))
            } else {
                volumes
            }
        }),
        affinity: rabbitmq.spec.affinity,
        tolerations: rabbitmq.spec.tolerations,
        ..PodSpecView::default()
    }
}

}
