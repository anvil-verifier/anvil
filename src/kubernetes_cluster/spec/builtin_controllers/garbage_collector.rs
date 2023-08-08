// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, error::*, object_meta::*, owner_reference::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::*, cluster::Cluster, message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn run_garbage_collector() -> BuiltinControllersAction {
    Action {
        precondition: |input: BuiltinControllersActionInput, s: BuiltinControllersState| {
            &&& input.choice.is_GarbageCollector()
            &&& input.resources.dom().contains(input.key)
            &&& input.resources[input.key].metadata.owner_references.is_Some()
            &&& input.resources[input.key].metadata.owner_references.get_Some_0().len() > 0
        },
        transition: |input: BuiltinControllersActionInput, s: BuiltinControllersState| {
            let resources = input.resources;
            let key = input.key;
            let namespace = resources[key].metadata.namespace.get_Some_0();
            let owner_references = resources[key].metadata.owner_references.get_Some_0();
            if forall |i| #![trigger owner_references[i]] {
                ||| !resources.dom().contains(owner_reference_to_object_reference(owner_references[i], namespace))
                ||| resources[owner_reference_to_object_reference(owner_references[i], namespace)].metadata.uid.get_Some_0() != owner_references[i].uid
            } {
                let delete_req_msg = built_in_controller_req_msg(delete_req_msg_content(
                    key, input.rest_id_allocator.allocate().1
                ));
                (s, (Multiset::singleton(delete_req_msg), input.rest_id_allocator.allocate().0))
            } else {
                (s, (Multiset::empty(), input.rest_id_allocator))
            }
        },
    }
}

}

}
