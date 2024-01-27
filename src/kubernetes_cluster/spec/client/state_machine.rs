// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::types::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::resource::*;
use crate::kubernetes_cluster::spec::{cluster::Cluster, message::*};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn create_custom_resource() -> ClientAction<E::Input, E::Output> {
    Action {
        precondition: |input: ClientActionInput, s: ClientState| {
            &&& input.obj.metadata.name.is_Some()
            &&& input.obj.metadata.namespace.is_Some()
            &&& (input.obj.kind == K::kind() || R::expect_from_user(input.obj))
        },
        transition: |input: ClientActionInput, s: ClientState| {
            let create_req_msg = Message::client_req_msg(Message::create_req_msg_content(
                input.obj.metadata.namespace.get_Some_0(),
                input.obj,
                input.rest_id_allocator.allocate().1
            ));

            let s_prime = s;
            let output = ClientActionOutput {
                send: Multiset::singleton(create_req_msg),
                rest_id_allocator: input.rest_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn delete_custom_resource() -> ClientAction<E::Input, E::Output> {
    Action {
        precondition: |input: ClientActionInput, s: ClientState| {
            &&& input.obj.metadata.name.is_Some()
            &&& input.obj.metadata.namespace.is_Some()
            &&& (input.obj.kind == K::kind() || R::expect_from_user(input.obj))
        },
        transition: |input: ClientActionInput, s: ClientState| {
            let delete_req_msg = Message::client_req_msg(Message::delete_req_msg_content(
                input.obj.object_ref(), input.rest_id_allocator.allocate().1
            ));

            let s_prime = s;
            let output = ClientActionOutput {
                send: Multiset::singleton(delete_req_msg),
                rest_id_allocator: input.rest_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn update_custom_resource() -> ClientAction<E::Input, E::Output> {
    Action {
        precondition: |input: ClientActionInput, s: ClientState| {
            &&& input.obj.metadata.name.is_Some()
            &&& input.obj.metadata.namespace.is_Some()
            &&& (input.obj.kind == K::kind() || R::expect_from_user(input.obj))
        },
        transition: |input: ClientActionInput, s: ClientState| {
            let update_req_msg = Message::client_req_msg(Message::update_req_msg_content(
                input.obj.metadata.namespace.get_Some_0(), input.obj.metadata.name.get_Some_0(), input.obj, input.rest_id_allocator.allocate().1
            ));

            let s_prime = s;
            let output = ClientActionOutput {
                send: Multiset::singleton(update_req_msg),
                rest_id_allocator: input.rest_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn client() -> ClientStateMachine<E::Input, E::Output> {
    StateMachine {
        init: |s: ClientState| {
            true
        },
        actions: set![Self::create_custom_resource(), Self::delete_custom_resource(), Self::update_custom_resource()],
        step_to_action: |step: Step| {
            match step {
                Step::CreateCustomResource(_) => Self::create_custom_resource(),
                Step::UpdateCustomResource(_) => Self::update_custom_resource(),
                Step::DeleteCustomResource(_) => Self::delete_custom_resource(),
            }
        },
        action_input: |step: Step, input: RestIdAllocator| {
            match step {
                Step::CreateCustomResource(obj) => ClientActionInput{ obj: obj, rest_id_allocator: input },
                Step::UpdateCustomResource(obj) => ClientActionInput{ obj: obj, rest_id_allocator: input },
                Step::DeleteCustomResource(obj) => ClientActionInput{ obj: obj, rest_id_allocator: input },
            }
        }
    }
}

}
}
