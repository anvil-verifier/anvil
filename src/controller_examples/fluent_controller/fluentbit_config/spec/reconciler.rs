// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::common::*;
use crate::fluent_controller::fluentbit_config::spec::resource::*;
use crate::fluent_controller::fluentbit_config::spec::types::*;
use crate::kubernetes_api_objects::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use vstd::{prelude::*, string::*};

verus! {

pub struct FluentBitConfigReconciler {}

impl Reconciler<FluentBitConfigView, EmptyAPI> for FluentBitConfigReconciler {
    type T = FluentBitConfigReconcileState;

    open spec fn reconcile_init_state() -> FluentBitConfigReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        fbc: FluentBitConfigView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitConfigReconcileState
    ) -> (FluentBitConfigReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(fbc, resp_o, state)
    }

    open spec fn reconcile_done(state: FluentBitConfigReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: FluentBitConfigReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool {
        false // Don't expect anything from the user except the cr object
    }
}

pub open spec fn reconcile_init_state() -> FluentBitConfigReconcileState {
    FluentBitConfigReconcileState {
        reconcile_step: FluentBitConfigReconcileStep::Init,
    }
}

pub open spec fn reconcile_done(state: FluentBitConfigReconcileState) -> bool {
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: FluentBitConfigReconcileState) -> bool {
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(
    fbc: FluentBitConfigView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitConfigReconcileState
) -> (FluentBitConfigReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        fbc.well_formed(),
{
    let step = state.reconcile_step;
    let resp = resp_o.get_Some_0();
    let fbc_name = fbc.metadata.name.get_Some_0();
    let fbc_namespace = fbc.metadata.namespace.get_Some_0();
    match step {
        FluentBitConfigReconcileStep::Init => {
            let req_o = APIRequest::GetRequest(SecretBuilder::get_request(fbc));
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Secret),
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        FluentBitConfigReconcileStep::AfterKRequestStep(_, resource) => {
            match resource {
                SubResource::Secret => { reconcile_helper::<SecretBuilder>(fbc, resp_o, state) },
            }
        },
        _ => {
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: step,
                ..state
            };
            (state_prime, None)
        }
    }
}

pub open spec fn reconcile_error_result(state: FluentBitConfigReconcileState) -> (FluentBitConfigReconcileState, Option<APIRequest>) {
    let state_prime = FluentBitConfigReconcileState {
        reconcile_step: FluentBitConfigReconcileStep::Error,
        ..state
    };
    let req_o = None;
    (state_prime, req_o)
}

pub open spec fn reconcile_helper<Builder: ResourceBuilder<FluentBitConfigView, FluentBitConfigReconcileState>>(
    fb: FluentBitConfigView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitConfigReconcileState
) -> (FluentBitConfigReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        fb.well_formed(),
        state.reconcile_step.is_AfterKRequestStep(),
{
    let step = state.reconcile_step;
    match step {
        FluentBitConfigReconcileStep::AfterKRequestStep(action, resource) => {
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
                                let state_prime = FluentBitConfigReconcileState {
                                    reconcile_step: FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Update, resource),
                                    ..state
                                };
                                (state_prime, Some(RequestView::KRequest(req_o)))
                            } else {
                                let state_prime = FluentBitConfigReconcileState {
                                    reconcile_step: FluentBitConfigReconcileStep::Error,
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
                                let state_prime = FluentBitConfigReconcileState {
                                    reconcile_step: FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Create, resource),
                                    ..state
                                };
                                (state_prime, Some(RequestView::KRequest(req_o)))
                            } else {
                                let state_prime = FluentBitConfigReconcileState {
                                    reconcile_step: FluentBitConfigReconcileStep::Error,
                                    ..state
                                };
                                (state_prime, None)
                            }
                        } else {
                            let state_prime = FluentBitConfigReconcileState {
                                reconcile_step: FluentBitConfigReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        // return error state
                        let state_prime = FluentBitConfigReconcileState {
                            reconcile_step: FluentBitConfigReconcileStep::Error,
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
                            let state_prime_with_next_step = FluentBitConfigReconcileState {
                                reconcile_step: next_step,
                                ..state_prime.get_Ok_0()
                            };
                            let req = if req_opt.is_Some() { Some(RequestView::KRequest(APIRequest::GetRequest(req_opt.get_Some_0()))) } else { None };
                            (state_prime_with_next_step, req)
                        } else {
                            let state_prime = FluentBitConfigReconcileState {
                                reconcile_step: FluentBitConfigReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        // return error state
                        let state_prime = FluentBitConfigReconcileState {
                            reconcile_step: FluentBitConfigReconcileStep::Error,
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
                            let state_prime_with_next_step = FluentBitConfigReconcileState {
                                reconcile_step: next_step,
                                ..state_prime.get_Ok_0()
                            };
                            let req = if req_opt.is_Some() { Some(RequestView::KRequest(APIRequest::GetRequest(req_opt.get_Some_0()))) } else { None };
                            (state_prime_with_next_step, req)
                        } else {
                            let state_prime = FluentBitConfigReconcileState {
                                reconcile_step: FluentBitConfigReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        // return error state
                        let state_prime = FluentBitConfigReconcileState {
                            reconcile_step: FluentBitConfigReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                },
            }
        },
        _ => {
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::Error,
                ..state
            };
            (state_prime, None)
        },
    }
}

pub open spec fn next_resource_get_step_and_request(fb: FluentBitConfigView, sub_resource: SubResource) -> (FluentBitConfigReconcileStep, Option<GetRequest>) {
    match sub_resource {
        SubResource::Secret => (FluentBitConfigReconcileStep::Done, None),
    }
}

pub open spec fn after_get_k_request_step(sub_resource: SubResource) -> FluentBitConfigReconcileStep {
    FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource)
}

}
