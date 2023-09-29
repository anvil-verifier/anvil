// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::prelude::*;
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::*, cluster::Cluster, kubernetes_api::common::KubernetesAPIState,
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn run_stabilizer() -> BuiltinControllersAction<E::Input, E::Output> {
    Action {
        precondition: |input: BuiltinControllersActionInput, s: KubernetesAPIState| {
            let key = input.key;
            &&& input.choice.is_Stabilizer()
            // Only stabilize the object that already exists
            &&& s.resources.contains_key(key)
        },
        transition: |input: BuiltinControllersActionInput, s: KubernetesAPIState| {
            let key = input.key;
            let s_prime = KubernetesAPIState {
                stable_resources: s.stable_resources.insert(key),
                ..s
            };
            let output = BuiltinControllersActionOutput {
                send: Multiset::empty(),
                rest_id_allocator: input.rest_id_allocator,
            };
            (s_prime, output)
        },
    }
}

}

}
