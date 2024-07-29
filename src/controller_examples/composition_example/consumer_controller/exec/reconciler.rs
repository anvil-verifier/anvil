// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::consumer_controller::model::reconciler as model_reconciler;
use crate::consumer_controller::trusted::exec_types::*;
use crate::consumer_controller::trusted::spec_types;
use crate::consumer_controller::trusted::step::*;
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_api_objects::spec::prelude::DynamicObjectView;
use crate::kubernetes_api_objects::spec::prelude::PodView;
use crate::kubernetes_api_objects::spec::resource::ResourceView;
use crate::producer_controller::trusted::exec_types::*;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ConsumerReconciler {}

impl Reconciler for ConsumerReconciler {
    type R = Consumer;
    type T = ConsumerReconcileState;
    type ExternalAPIType = EmptyAPIShimLayer;

    open spec fn well_formed(consumer: &Consumer) -> bool { consumer@.well_formed() }

    fn reconcile_init_state() -> ConsumerReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(consumer: &Consumer, resp_o: Option<Response<EmptyType>>, state: ConsumerReconcileState) -> (ConsumerReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(consumer, resp_o, state)
    }

    fn reconcile_done(state: &ConsumerReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(state: &ConsumerReconcileState) -> bool {
        reconcile_error(state)
    }
}

#[verifier(external_body)]
pub fn reconcile_init_state() -> (state: ConsumerReconcileState)
    ensures state@ == model_reconciler::reconcile_init_state(),
{
    ConsumerReconcileState {
        reconcile_step: ConsumerReconcileStep::Init,
    }
}

#[verifier(external_body)]
pub fn reconcile_done(state: &ConsumerReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_done(state@),
{
    match state.reconcile_step {
        ConsumerReconcileStep::Done => true,
        _ => false,
    }
}

#[verifier(external_body)]
pub fn reconcile_error(state: &ConsumerReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_error(state@),
{
    match state.reconcile_step {
        ConsumerReconcileStep::Error => true,
        _ => false,
    }
}

#[verifier(external_body)]
pub fn reconcile_core(consumer: &Consumer, resp_o: Option<Response<EmptyType>>, state: ConsumerReconcileState) -> (res: (ConsumerReconcileState, Option<Request<EmptyType>>))
    requires consumer@.well_formed(),
    ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_core(consumer@, opt_response_to_view(&resp_o), state@),
{
    let namespace = consumer.metadata().namespace().unwrap();
    match &state.reconcile_step {
        ConsumerReconcileStep::Init => {
            let req = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: Producer::api_resource(),
                name: consumer.metadata().name().unwrap(),
                namespace: consumer.metadata().namespace().unwrap(),
            });
            let state_prime = ConsumerReconcileState {
                reconcile_step: ConsumerReconcileStep::AfterGetProducer,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req)));
        },
        ConsumerReconcileStep::AfterGetProducer => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_producer_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_producer_resp.is_ok() {
                    let req = KubeAPIRequest::GetRequest(KubeGetRequest {
                        api_resource: Pod::api_resource(),
                        name: consumer.metadata().name().unwrap(),
                        namespace: consumer.metadata().namespace().unwrap(),
                    });
                    let state_prime = ConsumerReconcileState {
                        reconcile_step: ConsumerReconcileStep::AfterGetPod,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req)));
                } else if get_producer_resp.unwrap_err().is_object_not_found() {
                    let producer = make_producer(consumer);
                    let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Producer::api_resource(),
                        namespace: namespace,
                        obj: producer.marshal(),
                    });
                    let state_prime = ConsumerReconcileState {
                        reconcile_step: ConsumerReconcileStep::AfterCreateProducer,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req)));
                }
            }
            return (error_state(state), None);
        },
        ConsumerReconcileStep::AfterCreateProducer => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response() {
                let create_producer_resp = resp_o.unwrap().into_k_response().into_create_response().res;
                if create_producer_resp.is_ok() {
                    let req = KubeAPIRequest::GetRequest(KubeGetRequest {
                        api_resource: Pod::api_resource(),
                        name: consumer.metadata().name().unwrap(),
                        namespace: consumer.metadata().namespace().unwrap(),
                    });
                    let state_prime = ConsumerReconcileState {
                        reconcile_step: ConsumerReconcileStep::AfterGetPod,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req)));
                }
            }
            return (error_state(state), None);
        },
        ConsumerReconcileStep::AfterGetPod => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_pod_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_pod_resp.is_ok() {
                    let old_obj_unmarshal_res = Pod::unmarshal(get_pod_resp.unwrap());
                    if old_obj_unmarshal_res.is_ok() {
                        let old_pod = old_obj_unmarshal_res.unwrap();
                        let new_pod = update_pod(consumer, old_pod);
                        let req = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: Pod::api_resource(),
                            name: consumer.metadata().name().unwrap(),
                            namespace: consumer.metadata().namespace().unwrap(),
                            obj: new_pod.marshal(),
                        });
                        let state_prime = ConsumerReconcileState {
                            reconcile_step: ConsumerReconcileStep::AfterUpdatePod,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req)));
                    }
                }
            }
            return (error_state(state), None);
        },
        ConsumerReconcileStep::AfterUpdatePod => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response() {
                let update_pod_resp = resp_o.unwrap().into_k_response().into_update_response().res;
                if update_pod_resp.is_ok() {
                    let state_prime = ConsumerReconcileState {
                        reconcile_step: ConsumerReconcileStep::Done,
                        ..state
                    };
                    return (state_prime, None);
                }
            }
            return (error_state(state), None);
        },
        _ => {
            return (state, None);
        }
    }
}

pub fn error_state(state: ConsumerReconcileState) -> (state_prime: ConsumerReconcileState)
    // ensures state_prime@ == model_reconciler::error_state(state@),
{
    ConsumerReconcileState {
        reconcile_step: ConsumerReconcileStep::Error,
        ..state
    }
}

#[verifier(external_body)]
pub fn make_owner_references(consumer: &Consumer) -> (owner_references: Vec<OwnerReference>)
    requires consumer@.well_formed(),
    ensures owner_references@.map_values(|or: OwnerReference| or@) ==  model_reconciler::make_owner_references(consumer@),
{
    let mut owner_references = Vec::new();
    owner_references.push(consumer.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
            model_reconciler::make_owner_references(consumer@)
        );
    }
    owner_references
}

#[verifier(external_body)]
fn update_pod(consumer: &Consumer, pod: Pod) -> (new_pod: Pod)
{
    let mut new_pod = pod.clone();
    new_pod.set_metadata({
        let mut metadata = new_pod.metadata();
        metadata.set_labels({
            let mut labels = if metadata.labels().is_none() {
                StringMap::empty()
            } else {
                metadata.labels().unwrap()
            };
            labels.insert("consumer_message".to_string(), consumer.spec().message());
            labels
        });
        metadata
    });
    new_pod
}

#[verifier(external_body)]
fn make_producer(consumer: &Consumer) -> (producer: Producer)
    // requires consumer@.well_formed(),
    // ensures pod@ == model_reconciler::make_producer(consumer@),
{
    let mut producer = Producer::default();
    producer.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(consumer.metadata().name().unwrap());
        metadata.set_owner_references(make_owner_references(consumer));
        metadata
    });
    producer.set_spec({
        let mut producer_spec = ProducerSpec::default();
        producer_spec.set_message(consumer.spec().message());
        producer_spec
    });
    producer
}

}
