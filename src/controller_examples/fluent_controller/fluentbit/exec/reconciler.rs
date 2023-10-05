// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::exec::resource::*;
use crate::fluent_controller::fluentbit::exec::types::*;
use crate::fluent_controller::fluentbit::spec::reconciler as fb_spec;
use crate::fluent_controller::fluentbit::spec::resource as spec_resource;
use crate::fluent_controller::fluentbit::spec::types as spec_types;
use crate::kubernetes_api_objects::prelude::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::reconciler::spec::resource_builder::ResourceBuilder as SpecResourceBuilder;
use crate::vstd_ext::{string_map::StringMap, string_view::*, to_view::*};
use vstd::{prelude::*, string::*};

verus! {

pub struct FluentBitReconciler {}

#[verifier(external)]
impl Reconciler<FluentBit, FluentBitReconcileState, EmptyType, EmptyType, EmptyAPIShimLayer> for FluentBitReconciler {
    fn reconcile_init_state(&self) -> FluentBitReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, fb: &FluentBit, resp_o: Option<Response<EmptyType>>, state: FluentBitReconcileState) -> (FluentBitReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(fb, resp_o, state)
    }

    fn reconcile_done(&self, state: &FluentBitReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(&self, state: &FluentBitReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for FluentBitReconciler {
    fn default() -> FluentBitReconciler { FluentBitReconciler{} }
}

pub fn reconcile_init_state() -> (state: FluentBitReconcileState)
    ensures
        state@ == fb_spec::reconcile_init_state(),
{
    FluentBitReconcileState {
        reconcile_step: FluentBitReconcileStep::Init,
    }
}

pub fn reconcile_done(state: &FluentBitReconcileState) -> (res: bool)
    ensures
        res == fb_spec::reconcile_done(state@),
{
    match state.reconcile_step {
        FluentBitReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &FluentBitReconcileState) -> (res: bool)
    ensures
        res == fb_spec::reconcile_error(state@),
{
    match state.reconcile_step {
        FluentBitReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(fb: &FluentBit, resp_o: Option<Response<EmptyType>>, state: FluentBitReconcileState) -> (res: (FluentBitReconcileState, Option<Request<EmptyType>>))
    requires
        fb@.well_formed(),
    ensures
        (res.0@, opt_request_to_view(&res.1)) == fb_spec::reconcile_core(fb@, opt_response_to_view(&resp_o), state@),
        resource_version_check(opt_response_to_view(&resp_o), opt_request_to_view(&res.1)),
{
    let step = state.reconcile_step;
    match step{
        FluentBitReconcileStep::Init => {
            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: Secret::api_resource(),
                name: fb.spec().fluentbit_config_name(),
                namespace: fb.metadata().namespace().unwrap(),
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterGetSecret,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        FluentBitReconcileStep::AfterGetSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_sts_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_sts_resp.is_ok() {
                    let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                        api_resource: Role::api_resource(),
                        name: make_role_name(fb),
                        namespace: fb.metadata().namespace().unwrap(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ServiceAccount),
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterKRequestStep(_, resource) => {
            match resource {
                SubResource::ServiceAccount => reconcile_helper::<spec_resource::ServiceAccountBuilder, ServiceAccountBuilder>(fb, resp_o, state),
                SubResource::Role => reconcile_helper::<spec_resource::RoleBuilder, RoleBuilder>(fb, resp_o, state),
                SubResource::RoleBinding => reconcile_helper::<spec_resource::RoleBindingBuilder, RoleBindingBuilder>(fb, resp_o, state),
                SubResource::DaemonSet => reconcile_helper::<spec_resource::DaemonSetBuilder, DaemonSetBuilder>(fb, resp_o, state),
            }
        },
        _ => {
            let state_prime = FluentBitReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = None;
            (state_prime, req_o)
        }
    }
}

pub fn reconcile_helper<
    SpecBuilder: SpecResourceBuilder<spec_types::FluentBitView, spec_types::FluentBitReconcileState>,
    Builder: ResourceBuilder<FluentBit, FluentBitReconcileState, SpecBuilder>
>(
    fb: &FluentBit, resp_o: Option<Response<EmptyType>>, state: FluentBitReconcileState
) -> (res: (FluentBitReconcileState, Option<Request<EmptyType>>))
    requires
        fb@.well_formed(),
        Builder::requirements(fb@),
        state.reconcile_step.is_AfterKRequestStep(),
    ensures
        (res.0@, opt_request_to_view(&res.1)) == fb_spec::reconcile_helper::<SpecBuilder>(fb@, opt_response_to_view(&resp_o), state@),
{
    let step = state.reconcile_step.clone();
    match step {
        FluentBitReconcileStep::AfterKRequestStep(action, resource) => {
            match action {
                ActionKind::Get => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                        let get_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                        if get_resp.is_ok() {
                            let new_obj = Builder::update(fb, &state, get_resp.unwrap());
                            if new_obj.is_ok() {
                                let updated_obj = new_obj.unwrap();
                                let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                                    api_resource: Builder::get_request(fb).api_resource,
                                    name: Builder::get_request(fb).name,
                                    namespace: fb.metadata().namespace().unwrap(),
                                    obj: updated_obj,
                                });
                                let state_prime = FluentBitReconcileState {
                                    reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Update, resource),
                                    ..state
                                };
                                return (state_prime, Some(Request::KRequest(req_o)));
                            }
                        } else if get_resp.unwrap_err().is_object_not_found() {
                            // create
                            let new_obj = Builder::make(fb, &state);
                            if new_obj.is_ok() {
                                let created_obj = new_obj.unwrap();
                                let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                                    api_resource: Builder::get_request(fb).api_resource,
                                    namespace: fb.metadata().namespace().unwrap(),
                                    obj: created_obj,
                                });
                                let state_prime = FluentBitReconcileState {
                                    reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Create, resource),
                                    ..state
                                };
                                return (state_prime, Some(Request::KRequest(req_o)));
                            }
                        }
                    }
                    // return error state
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
                },
                ActionKind::Create => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok() {
                        let state_prime = Builder::state_after_create_or_update(resp_o.unwrap().into_k_response().into_create_response().res.unwrap(), state.clone());
                        let (next_step, req_opt) = next_resource_get_step_and_request(fb, resource);
                        if state_prime.is_ok() {
                            let state_prime_with_next_step = FluentBitReconcileState {
                                reconcile_step: next_step,
                                ..state_prime.unwrap()
                            };
                            let req = if req_opt.is_some() { Some(Request::KRequest(KubeAPIRequest::GetRequest(req_opt.unwrap()))) } else { None };
                            return (state_prime_with_next_step, req);
                        }
                    }
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
                },
                ActionKind::Update => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok() {
                        let state_prime = Builder::state_after_create_or_update(resp_o.unwrap().into_k_response().into_update_response().res.unwrap(), state.clone());
                        let (next_step, req_opt) = next_resource_get_step_and_request(fb, resource);
                        if state_prime.is_ok() {
                            let state_prime_with_next_step = FluentBitReconcileState {
                                reconcile_step: next_step,
                                ..state_prime.unwrap()
                            };
                            let req = if req_opt.is_some() { Some(Request::KRequest(KubeAPIRequest::GetRequest(req_opt.unwrap()))) } else { None };
                            return (state_prime_with_next_step, req);
                        }
                    }
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
                },
            }
        },
        _ => {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
    }
}

fn next_resource_get_step_and_request(fb: &FluentBit, sub_resource: SubResource) -> (res: (FluentBitReconcileStep, Option<KubeGetRequest>))
    requires
        fb@.well_formed(),
    ensures
        res.1.is_Some() == fb_spec::next_resource_get_step_and_request(fb@, sub_resource).1.is_Some(),
        res.1.is_Some() ==> res.1.get_Some_0().to_view() == fb_spec::next_resource_get_step_and_request(fb@, sub_resource).1.get_Some_0(),
        res.0 == fb_spec::next_resource_get_step_and_request(fb@, sub_resource).0,
{
    match sub_resource {
        SubResource::ServiceAccount => (after_get_k_request_step(SubResource::Role), Some(RoleBuilder::get_request(fb))),
        SubResource::Role => (after_get_k_request_step(SubResource::RoleBinding), Some(RoleBindingBuilder::get_request(fb))),
        SubResource::RoleBinding => (after_get_k_request_step(SubResource::DaemonSet), Some(DaemonSetBuilder::get_request(fb))),
        _ => (FluentBitReconcileStep::Done, None),
    }
}

fn after_get_k_request_step(sub_resource: SubResource) -> (step: FluentBitReconcileStep)
    ensures
        step == fb_spec::after_get_k_request_step(sub_resource),
{
    FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource)
}

}
