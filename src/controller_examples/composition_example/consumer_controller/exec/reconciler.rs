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

impl Default for ConsumerReconciler {
    fn default() -> ConsumerReconciler { ConsumerReconciler{} }
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
                } else {
                    return (error_state(state), None);
                }
            }
            return (error_state(state), None);
        },
        // ConsumerReconcileStep::AfterCreateProducer => {

        // },
        // ConsumerReconcileStep::AfterGetPod => {

        // },
        // ConsumerReconcileStep::AfterUpdatePod => {

        // },
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
fn make_pod(consumer: &Consumer) -> (pod: Pod)
    requires consumer@.well_formed(),
    ensures pod@ == model_reconciler::make_pod(consumer@),
{
    let mut pod = Pod::default();
    pod.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(consumer.metadata().name().unwrap());
        metadata.set_owner_references(make_owner_references(consumer));
        metadata
    });
    pod.set_spec({
        let mut pod_spec = PodSpec::default();
        pod_spec.set_containers({
            let mut containers = Vec::new();
            containers.push({
                let mut container = Container::default();
                container.set_name("nginx".to_string());
                container.set_image("nginx:1.14.2".to_string());
                container.set_ports({
                    let mut ports = Vec::new();
                    ports.push({
                        let mut container_port = ContainerPort::default();
                        container_port.set_container_port(80);
                        container_port
                    });
                    ports
                });
                container
            });
            containers
        });
        pod_spec
    });
    pod
}

#[verifier(external_body)]
fn make_producer(consumer: &Consumer) -> (producer: Producer)
    // requires consumer@.well_formed(),
    // ensures pod@ == model_reconciler::make_pod(consumer@),
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
        producer_spec.set_message("hello".to_string());
        producer_spec
    });
    producer
}

}
