// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_api_objects::spec::prelude::DynamicObjectView;
use crate::kubernetes_api_objects::spec::prelude::PodView;
use crate::kubernetes_api_objects::spec::resource::ResourceView;
use crate::producer_controller::model::reconciler as model_reconciler;
use crate::producer_controller::trusted::exec_types::*;
use crate::producer_controller::trusted::spec_types;
use crate::producer_controller::trusted::step::*;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ProducerReconciler {}

impl Reconciler for ProducerReconciler {
    type R = Producer;
    type T = ProducerReconcileState;
    type ExternalAPIType = EmptyAPIShimLayer;

    open spec fn well_formed(producer: &Producer) -> bool { producer@.well_formed() }

    fn reconcile_init_state() -> ProducerReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(producer: &Producer, resp_o: Option<Response<EmptyType>>, state: ProducerReconcileState) -> (ProducerReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(producer, resp_o, state)
    }

    fn reconcile_done(state: &ProducerReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(state: &ProducerReconcileState) -> bool {
        reconcile_error(state)
    }
}

// impl Default for ProducerReconciler {
//     pub fn default() -> ProducerReconciler { ProducerReconciler{} }
// }

#[verifier(external_body)]
pub fn reconcile_init_state() -> (state: ProducerReconcileState)
    ensures state@ == model_reconciler::reconcile_init_state(),
{
    ProducerReconcileState {
        reconcile_step: ProducerReconcileStep::Init,
    }
}

#[verifier(external_body)]
pub fn reconcile_done(state: &ProducerReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_done(state@),
{
    match state.reconcile_step {
        ProducerReconcileStep::Done => true,
        _ => false,
    }
}

#[verifier(external_body)]
pub fn reconcile_error(state: &ProducerReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_error(state@),
{
    match state.reconcile_step {
        ProducerReconcileStep::Error => true,
        _ => false,
    }
}

#[verifier(external_body)]
pub fn reconcile_core(producer: &Producer, resp_o: Option<Response<EmptyType>>, state: ProducerReconcileState) -> (res: (ProducerReconcileState, Option<Request<EmptyType>>))
    requires producer@.well_formed(),
    ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_core(producer@, opt_response_to_view(&resp_o), state@),
{
    let namespace = producer.metadata().namespace().unwrap();
    match &state.reconcile_step {
        ProducerReconcileStep::Init => {
            let pod = make_pod(producer);
            let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: Pod::api_resource(),
                namespace: namespace,
                obj: pod.marshal(),
            });
            let state_prime = ProducerReconcileState {
                reconcile_step: ProducerReconcileStep::Done,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req)));
        },
        _ => {
            return (state, None);
        }
    }
}

#[verifier(external_body)]
pub fn make_owner_references(producer: &Producer) -> (owner_references: Vec<OwnerReference>)
    requires producer@.well_formed(),
    ensures owner_references@.map_values(|or: OwnerReference| or@) ==  model_reconciler::make_owner_references(producer@),
{
    let mut owner_references = Vec::new();
    owner_references.push(producer.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
            model_reconciler::make_owner_references(producer@)
        );
    }
    owner_references
}

#[verifier(external_body)]
fn make_pod(producer: &Producer) -> (pod: Pod)
    requires producer@.well_formed(),
    ensures pod@ == model_reconciler::make_pod(producer@),
{
    let mut pod = Pod::default();
    pod.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(producer.metadata().name().unwrap());
        metadata.set_owner_references(make_owner_references(producer));
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

}
