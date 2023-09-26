// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::resource::*;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

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

pub open spec fn reconcile_helper<Builder: ResourceBuilder>(
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
                    let update_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
                    if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
                    && update_resp.is_Ok() {
                        let state_prime = Builder::state_after_create_or_update(update_resp.get_Ok_0(), state);
                        if state_prime.is_Ok() {
                            let req_o = next_resource_get_request(rabbitmq, resource);
                            (state_prime.get_Ok_0(), if req_o.is_Some() { Some(RequestView::KRequest(APIRequest::GetRequest(req_o.get_Some_0()))) } else { None })
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
                        let state_prime = Builder::state_after_create_or_update(update_resp.get_Ok_0(), state);
                        if state_prime.is_Ok() {
                            let req_o = next_resource_get_request(rabbitmq, resource);
                            (state_prime.get_Ok_0(), if req_o.is_Some() { Some(RequestView::KRequest(APIRequest::GetRequest(req_o.get_Some_0()))) } else { None })
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

pub open spec fn next_resource_get_request(rabbitmq: RabbitmqClusterView, sub_resource: SubResource) -> Option<GetRequest> {
    match sub_resource {
        SubResource::HeadlessService => Some(ServiceBuilder::get_request(rabbitmq)),
        SubResource::Service => Some(ErlangCookieBuilder::get_request(rabbitmq)),
        SubResource::ErlangCookieSecret => Some(DefaultUserSecretBuilder::get_request(rabbitmq)),
        SubResource::DefaultUserSecret => Some(PluginsConfigMapBuilder::get_request(rabbitmq)),
        SubResource::PluginsConfigMap => Some(ServerConfigMapBuilder::get_request(rabbitmq)),
        SubResource::ServerConfigMap => Some(ServiceAccountBuilder::get_request(rabbitmq)),
        SubResource::ServiceAccount => Some(RoleBuilder::get_request(rabbitmq)),
        SubResource::Role => Some(RoleBindingBuilder::get_request(rabbitmq)),
        SubResource::RoleBinding => Some(StatefulSetBuilder::get_request(rabbitmq)),
        _ => None,
    }
}

}
