// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::spec::resource::*;
use crate::fluent_controller::fluentbit::spec::types::*;
use crate::kubernetes_api_objects::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use vstd::{prelude::*, string::*};

verus! {

pub struct FluentBitReconciler {}

impl Reconciler<FluentBitView, EmptyAPI> for FluentBitReconciler {
    type T = FluentBitReconcileState;

    open spec fn reconcile_init_state() -> FluentBitReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        fb: FluentBitView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitReconcileState
    ) -> (FluentBitReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(fb, resp_o, state)
    }

    open spec fn reconcile_done(state: FluentBitReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: FluentBitReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool {
        obj.kind == SecretView::kind() // expect the user might create some secret object
    }
}

pub open spec fn reconcile_init_state() -> FluentBitReconcileState {
    FluentBitReconcileState {
        reconcile_step: FluentBitReconcileStep::Init,
    }
}

pub open spec fn reconcile_done(state: FluentBitReconcileState) -> bool {
    match state.reconcile_step {
        FluentBitReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: FluentBitReconcileState) -> bool {
    match state.reconcile_step {
        FluentBitReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(
    fb: FluentBitView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitReconcileState
) -> (FluentBitReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        fb.well_formed(),
{
    let step = state.reconcile_step;
    let resp = resp_o.get_Some_0();
    let fb_name = fb.metadata.name.get_Some_0();
    let fb_namespace = fb.metadata.namespace.get_Some_0();
    match step{
        FluentBitReconcileStep::Init => {
            let req_o = APIRequest::GetRequest(GetRequest{
                key: ObjectRef {
                    kind: SecretView::kind(),
                    name: fb.spec.fluentbit_config_name,
                    namespace: fb.metadata.namespace.get_Some_0(),
                }
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterGetSecret,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        FluentBitReconcileStep::AfterGetSecret => {
            let get_secret_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse()
            && resp_o.get_Some_0().get_KResponse_0().is_GetResponse()
            && get_secret_resp.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_role_key(fb),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ServiceAccount),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterKRequestStep(_, resource) => {
            match resource {
                SubResource::ServiceAccount => { reconcile_helper::<ServiceAccountBuilder>(fb, resp_o, state) },
                SubResource::Role => { reconcile_helper::<RoleBuilder>(fb, resp_o, state) },
                SubResource::RoleBinding => { reconcile_helper::<RoleBindingBuilder>(fb, resp_o, state) },
                SubResource::DaemonSet => { reconcile_helper::<DaemonSetBuilder>(fb, resp_o, state) },
            }
        },
        _ => {
            let state_prime = FluentBitReconcileState {
                reconcile_step: step,
                ..state
            };
            (state_prime, None)
        }
    }
}

pub open spec fn reconcile_error_result(state: FluentBitReconcileState) -> (FluentBitReconcileState, Option<APIRequest>) {
    let state_prime = FluentBitReconcileState {
        reconcile_step: FluentBitReconcileStep::Error,
        ..state
    };
    let req_o = None;
    (state_prime, req_o)
}

pub open spec fn reconcile_helper<Builder: ResourceBuilder<FluentBitView, FluentBitReconcileState>>(
    fb: FluentBitView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitReconcileState
) -> (FluentBitReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        fb.well_formed(),
        state.reconcile_step.is_AfterKRequestStep(),
{
    let step = state.reconcile_step;
    match step {
        FluentBitReconcileStep::AfterKRequestStep(action, resource) => {
            match action {
                ActionKind::Get => {
                    if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                        let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                        if get_resp.is_Ok() {
                            // update
                            let new_obj = Builder::update(fb, state, get_resp.get_Ok_0());
                            if new_obj.is_Ok() {
                                let updated_obj = new_obj.get_Ok_0();
                                let req_o = APIRequest::UpdateRequest(UpdateRequest {
                                    namespace: fb.metadata.namespace.get_Some_0(),
                                    name: Builder::get_request(fb).key.name,
                                    obj: updated_obj,
                                });
                                let state_prime = FluentBitReconcileState {
                                    reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Update, resource),
                                    ..state
                                };
                                (state_prime, Some(RequestView::KRequest(req_o)))
                            } else {
                                let state_prime = FluentBitReconcileState {
                                    reconcile_step: FluentBitReconcileStep::Error,
                                    ..state
                                };
                                (state_prime, None)
                            }
                        } else if get_resp.get_Err_0().is_ObjectNotFound() {
                            let new_obj = Builder::make(fb, state);
                            if new_obj.is_Ok() {
                                let req_o = APIRequest::CreateRequest(CreateRequest {
                                    namespace: fb.metadata.namespace.get_Some_0(),
                                    obj: new_obj.get_Ok_0(),
                                });
                                let state_prime = FluentBitReconcileState {
                                    reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Create, resource),
                                    ..state
                                };
                                (state_prime, Some(RequestView::KRequest(req_o)))
                            } else {
                                let state_prime = FluentBitReconcileState {
                                    reconcile_step: FluentBitReconcileStep::Error,
                                    ..state
                                };
                                (state_prime, None)
                            }
                        } else {
                            let state_prime = FluentBitReconcileState {
                                reconcile_step: FluentBitReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        // return error state
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                },
                ActionKind::Create => {
                    let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
                    if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
                    && create_resp.is_Ok() {
                        let state_prime = Builder::state_after_create_or_update(create_resp.get_Ok_0(), state);
                        if state_prime.is_Ok() {
                            let (next_step, req_opt) = next_resource_get_step_and_request(fb, resource);
                            let state_prime_with_next_step = FluentBitReconcileState {
                                reconcile_step: next_step,
                                ..state_prime.get_Ok_0()
                            };
                            let req = if req_opt.is_Some() { Some(RequestView::KRequest(APIRequest::GetRequest(req_opt.get_Some_0()))) } else { None };
                            (state_prime_with_next_step, req)
                        } else {
                            let state_prime = FluentBitReconcileState {
                                reconcile_step: FluentBitReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        // return error state
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::Error,
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
                            let (next_step, req_opt) = next_resource_get_step_and_request(fb, resource);
                            let state_prime_with_next_step = FluentBitReconcileState {
                                reconcile_step: next_step,
                                ..state_prime.get_Ok_0()
                            };
                            let req = if req_opt.is_Some() { Some(RequestView::KRequest(APIRequest::GetRequest(req_opt.get_Some_0()))) } else { None };
                            (state_prime_with_next_step, req)
                        } else {
                            let state_prime = FluentBitReconcileState {
                                reconcile_step: FluentBitReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        // return error state
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                },
            }
        },
        _ => {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            (state_prime, None)
        },
    }
}

pub open spec fn next_resource_get_step_and_request(fb: FluentBitView, sub_resource: SubResource) -> (FluentBitReconcileStep, Option<GetRequest>) {
    match sub_resource {
        SubResource::ServiceAccount => (after_get_k_request_step(SubResource::Role), Some(RoleBuilder::get_request(fb))),
        SubResource::Role => (after_get_k_request_step(SubResource::RoleBinding), Some(RoleBindingBuilder::get_request(fb))),
        SubResource::RoleBinding => (after_get_k_request_step(SubResource::DaemonSet), Some(DaemonSetBuilder::get_request(fb))),
        _ => (FluentBitReconcileStep::Done, None),
    }
}

pub open spec fn after_get_k_request_step(sub_resource: SubResource) -> FluentBitReconcileStep {
    FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource)
}

}
