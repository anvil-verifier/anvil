// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::resource::ResourceView;
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct ClientState {}

pub enum Step {
    CreateCustomResource,
    UpdateCustomResource,
    DeleteCustomResource,
}

pub struct ClientActionInput<K> {
    pub recv: Option<Message>,
    pub cr: K,
    pub rest_id_allocator: RestIdAllocator,
}

pub type ClientActionOutput = (Multiset<Message>, RestIdAllocator);

pub type ClientStateMachine<K> = StateMachine<ClientState, ClientActionInput<K>, ClientActionInput<K>, ClientActionOutput, Step>;

pub type ClientAction<K> = Action<ClientState, ClientActionInput<K>, ClientActionOutput>;

pub open spec fn client_req_msg(msg_content: MessageContent) -> Message {
    form_msg(HostId::Client, HostId::KubernetesAPI, msg_content)
}

pub open spec fn create_custom_resource<K: ResourceView>() -> ClientAction<K> {
    Action {
        precondition: |input: ClientActionInput<K>, s: ClientState| {
            input.recv.is_None()
        },
        transition: |input: ClientActionInput<K>, s: ClientState| {
            let create_req_msg = client_req_msg(create_req_msg_content(
                input.cr.metadata().namespace.get_Some_0(),
                input.cr.to_dynamic_object(),
                input.rest_id_allocator.allocate().1
            ));

            (ClientState{}, (Multiset::singleton(create_req_msg), input.rest_id_allocator.allocate().0))
        },
    }
}

pub open spec fn delete_custom_resource<K: ResourceView>() -> ClientAction<K> {
    Action {
        precondition: |input: ClientActionInput<K>, s: ClientState| {
            input.recv.is_None()
        },
        transition: |input: ClientActionInput<K>, s: ClientState| {
            let delete_req_msg = client_req_msg(delete_req_msg_content(
                input.cr.object_ref(), input.rest_id_allocator.allocate().1
            ));

            (ClientState{}, (Multiset::singleton(delete_req_msg), input.rest_id_allocator.allocate().0))
        },
    }
}

pub open spec fn update_custom_resource<K: ResourceView>() -> ClientAction<K> {
    Action {
        precondition: |input: ClientActionInput<K>, s: ClientState| {
            input.recv.is_None()
        },
        transition: |input: ClientActionInput<K>, s: ClientState| {
            let update_req_msg = client_req_msg(update_req_msg_content(
                input.cr.object_ref(), input.cr.to_dynamic_object(), input.rest_id_allocator.allocate().1
            ));

            (ClientState{}, (Multiset::singleton(update_req_msg), input.rest_id_allocator.allocate().0))
        },
    }
}

pub open spec fn client<K: ResourceView>() -> ClientStateMachine<K> {
    StateMachine {
        init: |s: ClientState| {
            true
        },
        actions: set![create_custom_resource(), delete_custom_resource(), update_custom_resource()],
        step_to_action: |step: Step| {
            match step {
                Step::CreateCustomResource => create_custom_resource(),
                Step::UpdateCustomResource => update_custom_resource(),
                Step::DeleteCustomResource => delete_custom_resource(),
            }
        },
        action_input: |step: Step, input: ClientActionInput<K>| {
            input
        }
    }
}

}
