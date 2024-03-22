// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::rabbitmq_controller::exec::resource::*;
use crate::rabbitmq_controller::model::reconciler as model_reconciler;
use crate::rabbitmq_controller::model::resource as model_resource;
use crate::rabbitmq_controller::trusted::exec_types::*;
use crate::rabbitmq_controller::trusted::spec_types;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::reconciler::spec::resource_builder::ResourceBuilder as SpecResourceBuilder;
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct RabbitmqReconciler {}

impl Reconciler for RabbitmqReconciler {
    type R = RabbitmqCluster;
    type T = RabbitmqReconcileState;
    type ExternalAPIType = EmptyAPIShimLayer;

    open spec fn well_formed(rabbitmq: &RabbitmqCluster) -> bool { rabbitmq@.well_formed() }

    fn reconcile_init_state() -> RabbitmqReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(rabbitmq: &RabbitmqCluster, resp_o: Option<Response<EmptyType>>, state: RabbitmqReconcileState) -> (RabbitmqReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(rabbitmq, resp_o, state)
    }

    fn reconcile_done(state: &RabbitmqReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(state: &RabbitmqReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for RabbitmqReconciler {
    fn default() -> RabbitmqReconciler { RabbitmqReconciler{} }
}

pub fn reconcile_init_state() -> (state: RabbitmqReconcileState)
    ensures state@ == model_reconciler::reconcile_init_state(),
{
    RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Init,
        latest_config_map_rv_opt: None,
    }
}

pub fn reconcile_done(state: &RabbitmqReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_done(state@),
{
    match state.reconcile_step {
        RabbitmqReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &RabbitmqReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_error(state@),
{
    match state.reconcile_step {
        RabbitmqReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(rabbitmq: &RabbitmqCluster, resp_o: Option<Response<EmptyType>>, state: RabbitmqReconcileState) -> (res: (RabbitmqReconcileState, Option<Request<EmptyType>>))
    requires rabbitmq@.well_formed(),
    ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_core(rabbitmq@, opt_response_to_view(&resp_o), state@),
        // resource_version_check(opt_response_to_view(&resp_o), opt_request_to_view(&res.1)),
{
    match &state.reconcile_step {
        RabbitmqReconcileStep::Init => {
            let req_o = KubeAPIRequest::GetRequest(HeadlessServiceBuilder::get_request(rabbitmq));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::HeadlessService),
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterKRequestStep(_, resource) => {
            match resource {
                SubResource::HeadlessService => reconcile_helper::<model_resource::HeadlessServiceBuilder, HeadlessServiceBuilder>(rabbitmq, resp_o, state),
                SubResource::Service => reconcile_helper::<model_resource::ServiceBuilder, ServiceBuilder>(rabbitmq, resp_o, state),
                SubResource::ErlangCookieSecret => reconcile_helper::<model_resource::ErlangCookieBuilder, ErlangCookieBuilder>(rabbitmq, resp_o, state),
                SubResource::DefaultUserSecret => reconcile_helper::<model_resource::DefaultUserSecretBuilder, DefaultUserSecretBuilder>(rabbitmq, resp_o, state),
                SubResource::PluginsConfigMap => reconcile_helper::<model_resource::PluginsConfigMapBuilder, PluginsConfigMapBuilder>(rabbitmq, resp_o, state),
                SubResource::ServerConfigMap => reconcile_helper::<model_resource::ServerConfigMapBuilder, ServerConfigMapBuilder>(rabbitmq, resp_o, state),
                SubResource::ServiceAccount => reconcile_helper::<model_resource::ServiceAccountBuilder, ServiceAccountBuilder>(rabbitmq, resp_o, state),
                SubResource::Role => reconcile_helper::<model_resource::RoleBuilder, RoleBuilder>(rabbitmq, resp_o, state),
                SubResource::RoleBinding => reconcile_helper::<model_resource::RoleBindingBuilder, RoleBindingBuilder>(rabbitmq, resp_o, state),
                SubResource::StatefulSet => reconcile_helper::<model_resource::StatefulSetBuilder, StatefulSetBuilder>(rabbitmq, resp_o, state),
            }
        },
        _ => {
            return (state, None);
        }
    }
}

pub fn reconcile_helper<
    SpecBuilder: SpecResourceBuilder<spec_types::RabbitmqClusterView, spec_types::RabbitmqReconcileState>,
    Builder: ResourceBuilder<RabbitmqCluster, RabbitmqReconcileState, SpecBuilder>
>(
    rabbitmq: &RabbitmqCluster, resp_o: Option<Response<EmptyType>>, state: RabbitmqReconcileState
) -> (res: (RabbitmqReconcileState, Option<Request<EmptyType>>))
    requires
        rabbitmq@.well_formed(),
        Builder::requirements(rabbitmq@),
        state.reconcile_step.is_AfterKRequestStep(),
    ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_helper::<SpecBuilder>(rabbitmq@, opt_response_to_view(&resp_o), state@),
{
    let step = state.reconcile_step.clone();
    match step {
        RabbitmqReconcileStep::AfterKRequestStep(action, resource) => {
            match action {
                ActionKind::Get => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                        let get_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                        if get_resp.is_ok() {
                            let new_obj = Builder::update(rabbitmq, &state, get_resp.unwrap());
                            if new_obj.is_ok() {
                                let updated_obj = new_obj.unwrap();
                                let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                                    api_resource: Builder::get_request(rabbitmq).api_resource,
                                    name: Builder::get_request(rabbitmq).name,
                                    namespace: rabbitmq.metadata().namespace().unwrap(),
                                    obj: updated_obj,
                                });
                                let state_prime = RabbitmqReconcileState {
                                    reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, resource),
                                    ..state
                                };
                                return (state_prime, Some(Request::KRequest(req_o)));
                            }
                        } else if get_resp.unwrap_err().is_object_not_found() {
                            // create
                            let new_obj = Builder::make(rabbitmq, &state);
                            if new_obj.is_ok() {
                                let created_obj = new_obj.unwrap();
                                let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                                    api_resource: Builder::get_request(rabbitmq).api_resource,
                                    namespace: rabbitmq.metadata().namespace().unwrap(),
                                    obj: created_obj,
                                });
                                let state_prime = RabbitmqReconcileState {
                                    reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, resource),
                                    ..state
                                };
                                return (state_prime, Some(Request::KRequest(req_o)));
                            }
                        }
                    }
                    // return error state
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
                },
                ActionKind::Create => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok() {
                        let next_state = Builder::state_after_create(rabbitmq, resp_o.unwrap().into_k_response().into_create_response().res.unwrap(), state.clone());
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
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    return (state_prime, None);
                },
                ActionKind::Update => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok() {
                        let next_state = Builder::state_after_update(rabbitmq, resp_o.unwrap().into_k_response().into_update_response().res.unwrap(), state.clone());
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
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    return (state_prime, None);
                },
            }
        },
        _ => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
    }
}

}
