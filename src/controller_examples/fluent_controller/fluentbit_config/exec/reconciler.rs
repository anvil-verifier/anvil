// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit_config::exec::resource::*;
use crate::fluent_controller::fluentbit_config::model::reconciler as model_reconciler;
use crate::fluent_controller::fluentbit_config::model::resource as model_resource;
use crate::fluent_controller::fluentbit_config::trusted::{exec_types::*, spec_types, step::*};
use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::reconciler::spec::resource_builder::ResourceBuilder as SpecResourceBuilder;
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

pub struct FluentBitConfigReconciler {}

impl Reconciler for FluentBitConfigReconciler {
    type R = FluentBitConfig;
    type T = FluentBitConfigReconcileState;
    type ExternalAPIType = EmptyAPIShimLayer;

    open spec fn well_formed(fbc: &FluentBitConfig) -> bool { fbc@.well_formed() }

    fn reconcile_init_state() -> FluentBitConfigReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(fbc: &FluentBitConfig, resp_o: Option<Response<EmptyType>>, state: FluentBitConfigReconcileState)
    -> (FluentBitConfigReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(fbc, resp_o, state)
    }

    fn reconcile_done(state: &FluentBitConfigReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(state: &FluentBitConfigReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for FluentBitConfigReconciler {
    fn default() -> FluentBitConfigReconciler { FluentBitConfigReconciler{} }
}

pub fn reconcile_init_state() -> (state: FluentBitConfigReconcileState)
    ensures state@ == model_reconciler::reconcile_init_state(),
{
    FluentBitConfigReconcileState { reconcile_step: FluentBitConfigReconcileStep::Init }
}

pub fn reconcile_done(state: &FluentBitConfigReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_done(state@),
{
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &FluentBitConfigReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_error(state@),
{
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(fbc: &FluentBitConfig, resp_o: Option<Response<EmptyType>>, state: FluentBitConfigReconcileState) -> (res: (FluentBitConfigReconcileState, Option<Request<EmptyType>>))
    requires fbc@.well_formed(),
    ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_core(fbc@, opt_response_to_view(&resp_o), state@),
{
    let step = state.reconcile_step;
    match step{
        FluentBitConfigReconcileStep::Init => {
            let req_o = KubeAPIRequest::GetRequest(SecretBuilder::get_request(fbc));
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Secret),
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        FluentBitConfigReconcileStep::AfterKRequestStep(_, resource) => {
            match resource {
                SubResource::Secret => reconcile_helper::<model_resource::SecretBuilder, SecretBuilder>(fbc, resp_o, state),
            }
        },
        _ => {
            let state_prime =FluentBitConfigReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = None;
            (state_prime, req_o)
        }
    }
}

pub fn reconcile_helper<
    SpecBuilder: SpecResourceBuilder<spec_types::FluentBitConfigView, spec_types::FluentBitConfigReconcileState>,
    Builder: ResourceBuilder<FluentBitConfig, FluentBitConfigReconcileState, SpecBuilder>
>(
    fbc: &FluentBitConfig, resp_o: Option<Response<EmptyType>>, state: FluentBitConfigReconcileState
) -> (res: (FluentBitConfigReconcileState, Option<Request<EmptyType>>))
    requires
        fbc@.well_formed(),
        Builder::requirements(fbc@),
        state.reconcile_step.is_AfterKRequestStep(),
    ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_helper::<SpecBuilder>(fbc@, opt_response_to_view(&resp_o), state@),
{
    let step = state.reconcile_step.clone();
    match step {
        FluentBitConfigReconcileStep::AfterKRequestStep(action, resource) => {
            match action {
                ActionKind::Get => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                        let get_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                        if get_resp.is_ok() {
                            let new_obj = Builder::update(fbc, &state, get_resp.unwrap());
                            if new_obj.is_ok() {
                                let updated_obj = new_obj.unwrap();
                                let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                                    api_resource: Builder::get_request(fbc).api_resource,
                                    name: Builder::get_request(fbc).name,
                                    namespace: fbc.metadata().namespace().unwrap(),
                                    obj: updated_obj,
                                });
                                let state_prime = FluentBitConfigReconcileState {
                                    reconcile_step: FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Update, resource),
                                    ..state
                                };
                                return (state_prime, Some(Request::KRequest(req_o)));
                            }
                        } else if get_resp.unwrap_err().is_object_not_found() {
                            // create
                            let new_obj = Builder::make(fbc, &state);
                            if new_obj.is_ok() {
                                let created_obj = new_obj.unwrap();
                                let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                                    api_resource: Builder::get_request(fbc).api_resource,
                                    namespace: fbc.metadata().namespace().unwrap(),
                                    obj: created_obj,
                                });
                                let state_prime = FluentBitConfigReconcileState {
                                    reconcile_step: FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Create, resource),
                                    ..state
                                };
                                return (state_prime, Some(Request::KRequest(req_o)));
                            }
                        }
                    }
                    // return error state
                    let state_prime = FluentBitConfigReconcileState {
                        reconcile_step: FluentBitConfigReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
                },
                ActionKind::Create => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok() {
                        let next_state = Builder::state_after_create(fbc, resp_o.unwrap().into_k_response().into_create_response().res.unwrap(), state.clone());
                        if next_state.is_ok() {
                            let (state_prime, req) = next_state.unwrap();
                            let req_o = if req.is_some() {
                                Some(Request::KRequest(req.unwrap()))
                            } else {
                                None
                            };
                            return (state_prime, req_o);
                        }
                    }
                    let state_prime = FluentBitConfigReconcileState {
                        reconcile_step: FluentBitConfigReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
                },
                ActionKind::Update => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok() {
                        let next_state = Builder::state_after_update(fbc, resp_o.unwrap().into_k_response().into_update_response().res.unwrap(), state.clone());
                        if next_state.is_ok() {
                            let (state_prime, req) = next_state.unwrap();
                            let req_o = if req.is_some() {
                                Some(Request::KRequest(req.unwrap()))
                            } else {
                                None
                            };
                            return (state_prime, req_o);
                        }
                    }
                    let state_prime = FluentBitConfigReconcileState {
                        reconcile_step: FluentBitConfigReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
                },
            }
        },
        _ => {
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
    }
}

}
