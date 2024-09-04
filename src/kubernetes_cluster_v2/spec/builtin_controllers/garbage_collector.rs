// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster_v2::spec::{
    api_server::types::APIServerState, builtin_controllers::types::*, message::*,
};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use vstd::{multiset::*, prelude::*};

verus! {

// TODO:
// + Specify foreground deletion
//
// + Specify orphan dependents

pub open spec fn run_garbage_collector() -> BuiltinControllersAction {
    Action {
        precondition: |input: BuiltinControllersActionInput, s: ()| {
            let resources = input.resources;
            let key = input.key;
            let owner_references = resources[key].metadata.owner_references.get_Some_0();
            // The garbage collector is chosen by the top level state machine
            &&& input.choice.is_GarbageCollector()
            // The object exists in the cluster state
            &&& resources.contains_key(input.key)
            // and it has at least one owner reference
            &&& resources[key].metadata.owner_references.is_Some()
            &&& resources[key].metadata.owner_references.get_Some_0().len() > 0
            // The garbage collector decides whether to delete an object by checking its owner references,
            // it deletes the object if for each owner reference...
            &&& forall |i| #![trigger owner_references[i]] 0 <= i < owner_references.len() ==> {
                // the referred owner object does not exist in the cluster state
                ||| !resources.contains_key(owner_reference_to_object_reference(owner_references[i], key.namespace))
                // or it exists but has a different uid
                // (which means the actual owner was deleted and another object with the same name gets created again)
                ||| resources[owner_reference_to_object_reference(owner_references[i], key.namespace)].metadata.uid != Some(owner_references[i].uid)
            }
        },
        transition: |input: BuiltinControllersActionInput, s: ()| {
            let delete_req_msg = Message::built_in_controller_req_msg(
                input.rest_id_allocator.allocate().1, Message::delete_req_msg_content(input.key)
            );
            let output = BuiltinControllersActionOutput {
                send: Multiset::singleton(delete_req_msg),
                rest_id_allocator: input.rest_id_allocator.allocate().0,
            };
            ((), output)
        },
    }
}

}
