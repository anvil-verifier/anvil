// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::resource::*;
use crate::rabbitmq_controller::trusted::maker::*;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

impl Reconciler<RabbitmqClusterView, EmptyAPI> for RabbitmqReconciler {
    type T = RabbitmqReconcileState;

    open spec fn reconcile_init_state() -> RabbitmqReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(rabbitmq: RabbitmqClusterView, resp_o: Option<ResponseView<EmptyTypeView>>, state: RabbitmqReconcileState)
    -> (RabbitmqReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(rabbitmq, resp_o, state)
    }

    open spec fn reconcile_done(state: RabbitmqReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: RabbitmqReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool { false /* Don't expect anything from the user except the cr object*/ }
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
    match step {
        RabbitmqReconcileStep::Init => {
            // get headless service
            let req_o = APIRequest::GetRequest(HeadlessServiceBuilder::get_request(rabbitmq));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::HeadlessService),
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterKRequestStep(_, resource) => {
            match resource {
                SubResource::HeadlessService => { reconcile_helper::<HeadlessServiceBuilder>(rabbitmq, resp_o, state) },
                SubResource::Service => { reconcile_helper::<ServiceBuilder>(rabbitmq, resp_o, state) },
                SubResource::ErlangCookieSecret => { reconcile_helper::<ErlangCookieBuilder>(rabbitmq, resp_o, state) },
                SubResource::DefaultUserSecret => { reconcile_helper::<DefaultUserSecretBuilder>(rabbitmq, resp_o, state) },
                SubResource::PluginsConfigMap => { reconcile_helper::<PluginsConfigMapBuilder>(rabbitmq, resp_o, state) },
                SubResource::ServerConfigMap => { reconcile_helper::<ServerConfigMapBuilder>(rabbitmq, resp_o, state) },
                SubResource::ServiceAccount => { reconcile_helper::<ServiceAccountBuilder>(rabbitmq, resp_o, state) },
                SubResource::Role => { reconcile_helper::<RoleBuilder>(rabbitmq, resp_o, state) },
                SubResource::RoleBinding => { reconcile_helper::<RoleBindingBuilder>(rabbitmq, resp_o, state) },
                SubResource::StatefulSet => { reconcile_helper::<StatefulSetBuilder>(rabbitmq, resp_o, state) },
            }
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

pub open spec fn reconcile_helper<Builder: ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState>>(
    rabbitmq: RabbitmqClusterView, resp_o: Option<ResponseView<EmptyTypeView>>, state: RabbitmqReconcileState
) -> (RabbitmqReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
        state.reconcile_step.is_AfterKRequestStep(),
{
    let step = state.reconcile_step;
    match step {
        RabbitmqReconcileStep::AfterKRequestStep(action, resource) => {
            match action {
                ActionKind::Get => {
                    if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                        let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                        if get_resp.is_Ok() {
                            // update
                            let new_obj = Builder::update(rabbitmq, state, get_resp.get_Ok_0());
                            if new_obj.is_Ok() {
                                let updated_obj = new_obj.get_Ok_0();
                                let req_o = APIRequest::UpdateRequest(UpdateRequest {
                                    namespace: rabbitmq.metadata.namespace.get_Some_0(),
                                    name: Builder::get_request(rabbitmq).key.name,
                                    obj: updated_obj,
                                });
                                let state_prime = RabbitmqReconcileState {
                                    reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, resource),
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
                        } else if get_resp.get_Err_0().is_ObjectNotFound() {
                            let new_obj = Builder::make(rabbitmq, state);
                            if new_obj.is_Ok() {
                                let req_o = APIRequest::CreateRequest(CreateRequest {
                                    namespace: rabbitmq.metadata.namespace.get_Some_0(),
                                    obj: new_obj.get_Ok_0(),
                                });
                                let state_prime = RabbitmqReconcileState {
                                    reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, resource),
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
                    } else {
                        // return error state
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                },
                ActionKind::Create => {
                    let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
                    if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
                    && create_resp.is_Ok() {
                        let next_state = Builder::state_after_create(rabbitmq, create_resp.get_Ok_0(), state);
                        if next_state.is_Ok() {
                            let (state_prime, req) = next_state.get_Ok_0();
                            let req_o = if req.is_Some() { Some(RequestView::KRequest(req.get_Some_0())) } else { None };
                            (state_prime, req_o)
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
                ActionKind::Update => {
                    let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
                    if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
                    && update_resp.is_Ok() {
                        let next_state = Builder::state_after_update(rabbitmq, update_resp.get_Ok_0(), state);
                        if next_state.is_Ok() {
                            let (state_prime, req) = next_state.get_Ok_0();
                            let req_o = if req.is_Some() { Some(RequestView::KRequest(req.get_Some_0())) } else { None };
                            (state_prime, req_o)
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
            }
        },
        _ => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            (state_prime, None)
        },
    }
}

pub struct RabbitmqMaker {}

impl Maker for RabbitmqMaker {
    open spec fn make_headless_service_key(rabbitmq: RabbitmqClusterView) -> ObjectRef { make_headless_service_key(rabbitmq) }

    open spec fn make_main_service_key(rabbitmq: RabbitmqClusterView) -> ObjectRef { make_main_service_key(rabbitmq) }

    open spec fn make_erlang_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef { make_erlang_secret_key(rabbitmq) }

    open spec fn make_default_user_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef { make_default_user_secret_key(rabbitmq) }

    open spec fn make_plugins_config_map_key(rabbitmq: RabbitmqClusterView) -> ObjectRef { make_plugins_config_map_key(rabbitmq) }

    open spec fn make_server_config_map_key(rabbitmq: RabbitmqClusterView) -> ObjectRef { make_server_config_map_key(rabbitmq) }

    open spec fn make_service_account_key(rabbitmq: RabbitmqClusterView) -> ObjectRef { make_service_account_key(rabbitmq) }

    open spec fn make_role_key(rabbitmq: RabbitmqClusterView) -> ObjectRef { make_role_key(rabbitmq) }

    open spec fn make_role_binding_key(rabbitmq: RabbitmqClusterView) -> ObjectRef { make_role_binding_key(rabbitmq) }

    open spec fn make_stateful_set_key(rabbitmq: RabbitmqClusterView) -> ObjectRef { make_stateful_set_key(rabbitmq) }

    open spec fn make_headless_service(rabbitmq: RabbitmqClusterView) -> ServiceView { make_headless_service(rabbitmq) }

    open spec fn make_main_service(rabbitmq: RabbitmqClusterView) -> ServiceView { make_main_service(rabbitmq) }

    open spec fn make_erlang_secret(rabbitmq: RabbitmqClusterView) -> SecretView { make_erlang_secret(rabbitmq) }

    open spec fn make_default_user_secret(rabbitmq: RabbitmqClusterView) -> SecretView { make_default_user_secret(rabbitmq) }

    open spec fn make_plugins_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView { make_plugins_config_map(rabbitmq) }

    open spec fn make_server_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView { make_server_config_map(rabbitmq) }

    open spec fn make_service_account(rabbitmq: RabbitmqClusterView) -> ServiceAccountView { make_service_account(rabbitmq) }

    open spec fn make_role(rabbitmq: RabbitmqClusterView) -> RoleView { make_role(rabbitmq) }

    open spec fn make_role_binding(rabbitmq: RabbitmqClusterView) -> RoleBindingView { make_role_binding(rabbitmq) }

    open spec fn make_stateful_set(rabbitmq: RabbitmqClusterView, config_map_rv: StringView) -> StatefulSetView { make_stateful_set(rabbitmq, config_map_rv) }
}

}
