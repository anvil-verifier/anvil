// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::resource::*;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::reconciler as rabbitmq_spec;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vstd_ext::{string_map::StringMap, string_view::*, to_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct RabbitmqReconciler {}

#[verifier(external)]
impl Reconciler<RabbitmqCluster, RabbitmqReconcileState, EmptyType, EmptyType, EmptyAPIShimLayer> for RabbitmqReconciler {
    fn reconcile_init_state(&self) -> RabbitmqReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, rabbitmq: &RabbitmqCluster, resp_o: Option<Response<EmptyType>>, state: RabbitmqReconcileState) -> (RabbitmqReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(rabbitmq, resp_o, state)
    }

    fn reconcile_done(&self, state: &RabbitmqReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(&self, state: &RabbitmqReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for RabbitmqReconciler {
    fn default() -> RabbitmqReconciler { RabbitmqReconciler{} }
}

pub fn reconcile_init_state() -> (state: RabbitmqReconcileState)
    ensures
        state@ == rabbitmq_spec::reconcile_init_state(),
{
    RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Init,
        latest_config_map_rv_opt: None,
    }
}

pub fn reconcile_done(state: &RabbitmqReconcileState) -> (res: bool)
    ensures
        res == rabbitmq_spec::reconcile_done(state@),
{
    match state.reconcile_step {
        RabbitmqReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &RabbitmqReconcileState) -> (res: bool)
    ensures
        res == rabbitmq_spec::reconcile_error(state@),
{
    match state.reconcile_step {
        RabbitmqReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(rabbitmq: &RabbitmqCluster, resp_o: Option<Response<EmptyType>>, state: RabbitmqReconcileState) -> (res: (RabbitmqReconcileState, Option<Request<EmptyType>>))
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        (res.0@, opt_request_to_view(&res.1)) == rabbitmq_spec::reconcile_core(rabbitmq@, opt_response_to_view(&resp_o), state@),
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
                SubResource::HeadlessService => {
                    reconcile_helper::<spec_resource::HeadlessServiceBuilder, HeadlessServiceBuilder>(rabbitmq, resp_o, state)
                },
                SubResource::Service => {
                    reconcile_helper::<spec_resource::ServiceBuilder, ServiceBuilder>(rabbitmq, resp_o, state)
                },
                SubResource::ErlangCookieSecret => {
                    reconcile_helper::<spec_resource::ErlangCookieBuilder, ErlangCookieBuilder>(rabbitmq, resp_o, state)
                },
                SubResource::DefaultUserSecret => {
                    reconcile_helper::<spec_resource::DefaultUserSecretBuilder, DefaultUserSecretBuilder>(rabbitmq, resp_o, state)
                },
                SubResource::PluginsConfigMap => {
                    reconcile_helper::<spec_resource::PluginsConfigMapBuilder, PluginsConfigMapBuilder>(rabbitmq, resp_o, state)
                },
                SubResource::ServerConfigMap => {
                    reconcile_helper::<spec_resource::ServerConfigMapBuilder, ServerConfigMapBuilder>(rabbitmq, resp_o, state)
                },
                SubResource::ServiceAccount => {
                    reconcile_helper::<spec_resource::ServiceAccountBuilder, ServiceAccountBuilder>(rabbitmq, resp_o, state)
                },
                SubResource::Role => {
                    reconcile_helper::<spec_resource::RoleBuilder, RoleBuilder>(rabbitmq, resp_o, state)
                },
                SubResource::RoleBinding => {
                    reconcile_helper::<spec_resource::RoleBindingBuilder, RoleBindingBuilder>(rabbitmq, resp_o, state)
                },
                SubResource::StatefulSet => {
                    reconcile_helper::<spec_resource::StatefulSetBuilder, StatefulSetBuilder>(rabbitmq, resp_o, state)
                },
            }
        },
        _ => {
            return (state, None);
        }
    }
}

pub fn reconcile_helper<
    SpecBuilder: spec_resource::ResourceBuilder,
    Builder: ResourceBuilder<SpecBuilder>
>(
    rabbitmq: &RabbitmqCluster, resp_o: Option<Response<EmptyType>>, state: RabbitmqReconcileState
) -> (res: (RabbitmqReconcileState, Option<Request<EmptyType>>))
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
        state.reconcile_step.is_AfterKRequestStep(),
    ensures
        (res.0@, opt_request_to_view(&res.1)) == rabbitmq_spec::reconcile_helper::<SpecBuilder>(rabbitmq@, opt_response_to_view(&resp_o), state@),
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
                                    namespace: rabbitmq.namespace().unwrap(),
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
                                    namespace: rabbitmq.namespace().unwrap(),
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
                        let state_prime = Builder::state_after_create_or_update(resp_o.unwrap().into_k_response().into_create_response().res.unwrap(), state.clone());
                        let req_o = next_resource_get_request(rabbitmq, resource);
                        if state_prime.is_ok() {
                            return (state_prime.unwrap(), if req_o.is_some() { Some(Request::KRequest(KubeAPIRequest::GetRequest(req_o.unwrap()))) } else { None });
                        }
                    }
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
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
                        let req_o = next_resource_get_request(rabbitmq, resource);
                        if state_prime.is_ok() {
                            return (state_prime.unwrap(), if req_o.is_some() { Some(Request::KRequest(KubeAPIRequest::GetRequest(req_o.unwrap()))) } else { None });
                        }
                    }
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
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

fn next_resource_get_request(rabbitmq: &RabbitmqCluster, sub_resource: SubResource) -> (res: Option<KubeGetRequest>)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        res.is_Some() == rabbitmq_spec::next_resource_get_request(rabbitmq@, sub_resource).is_Some(),
        res.is_Some() ==> res.get_Some_0().to_view() == rabbitmq_spec::next_resource_get_request(rabbitmq@, sub_resource).get_Some_0(),
{
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
