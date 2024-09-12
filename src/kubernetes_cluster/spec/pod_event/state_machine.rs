// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::types::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{pod::*, resource::*};
use crate::kubernetes_cluster::spec::{cluster::Cluster, message::*};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn create_pod() -> PodEventAction<E::Input, E::Output> {
    Action {
        precondition: |input: PodEventActionInput, s: PodEventState| {
            &&& s.enabled
            &&& input.obj.metadata.name.is_Some()
            &&& input.obj.metadata.namespace.is_Some()
            &&& input.obj.kind == PodView::kind()
            &&& PodView::unmarshal(input.obj).is_Ok()
        },
        transition: |input: PodEventActionInput, s: PodEventState| {
            let create_req_msg = Message::pod_event_req_msg(Message::create_req_msg_content(
                input.obj.metadata.namespace.get_Some_0(),
                input.obj,
                input.rest_id_allocator.allocate().1
            ));

            let s_prime = s;
            let output = PodEventActionOutput {
                send: Multiset::singleton(create_req_msg),
                rest_id_allocator: input.rest_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn delete_pod() -> PodEventAction<E::Input, E::Output> {
    Action {
        precondition: |input: PodEventActionInput, s: PodEventState| {
            &&& s.enabled
            &&& input.obj.metadata.name.is_Some()
            &&& input.obj.metadata.namespace.is_Some()
            &&& input.obj.kind == PodView::kind()
            &&& PodView::unmarshal(input.obj).is_Ok()
        },
        transition: |input: PodEventActionInput, s: PodEventState| {
            let delete_req_msg = Message::pod_event_req_msg(Message::delete_req_msg_content(
                input.obj.object_ref(), input.rest_id_allocator.allocate().1
            ));

            let s_prime = s;
            let output = PodEventActionOutput {
                send: Multiset::singleton(delete_req_msg),
                rest_id_allocator: input.rest_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

// NOTE: We don't need to model update_status, since its effect can be modeled
// as an update request.
pub open spec fn update_pod() -> PodEventAction<E::Input, E::Output> {
    Action {
        precondition: |input: PodEventActionInput, s: PodEventState| {
            &&& s.enabled
            &&& input.obj.metadata.name.is_Some()
            &&& input.obj.metadata.namespace.is_Some()
            &&& input.obj.kind == PodView::kind()
            &&& PodView::unmarshal(input.obj).is_Ok()
        },
        transition: |input: PodEventActionInput, s: PodEventState| {
            let update_req_msg = Message::pod_event_req_msg(Message::update_req_msg_content(
                input.obj.metadata.namespace.get_Some_0(), input.obj.metadata.name.get_Some_0(), input.obj, input.rest_id_allocator.allocate().1
            ));

            let s_prime = s;
            let output = PodEventActionOutput {
                send: Multiset::singleton(update_req_msg),
                rest_id_allocator: input.rest_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn pod_event() -> PodEventStateMachine<E::Input, E::Output> {
    StateMachine {
        init: |s: PodEventState| {
            s.enabled
        },
        actions: set![Self::create_pod(), Self::delete_pod(), Self::update_pod()],
        step_to_action: |step: Step| {
            match step {
                Step::CreatePod(_) => Self::create_pod(),
                Step::UpdatePod(_) => Self::update_pod(),
                Step::DeletePod(_) => Self::delete_pod(),
            }
        },
        action_input: |step: Step, input: RestIdAllocator| {
            match step {
                Step::CreatePod(obj) => PodEventActionInput{ obj: obj, rest_id_allocator: input },
                Step::UpdatePod(obj) => PodEventActionInput{ obj: obj, rest_id_allocator: input },
                Step::DeletePod(obj) => PodEventActionInput{ obj: obj, rest_id_allocator: input },
            }
        }
    }
}

}
}
