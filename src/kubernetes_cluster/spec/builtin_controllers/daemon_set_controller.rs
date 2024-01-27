// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::types::ApiServerState, builtin_controllers::types::*, cluster::Cluster, message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn run_daemon_set_controller() -> BuiltinControllersAction<E::Input, E::Output> {
    Action {
        precondition: |input: BuiltinControllersActionInput, s: ApiServerState| {
            let resources = s.resources;
            let key = input.key;
            let owner_references = resources[key].metadata.owner_references.get_Some_0();
            // The daemon set controller is chosen by the top level state machine
            &&& input.choice.is_DaemonSetController()
            // The object exists in the cluster state
            &&& resources.contains_key(key)
            // and it is a daemon set
            &&& key.kind == DaemonSetView::kind()
            // and it is not stable yet
            &&& !s.stable_resources.contains(key)
        },
        transition: |input: BuiltinControllersActionInput, s: ApiServerState| {
            let resources = s.resources;
            let key = input.key;
            let number_ready = input.choice.get_DaemonSetController_number_ready();
            let old_daemon_set = DaemonSetView::unmarshal(resources[key]).get_Ok_0();
            let new_daemon_set = DaemonSetView {
                status: Some(DaemonSetStatusView {
                    number_ready: number_ready,
                }),
                ..old_daemon_set
            };
            let update_status_req_msg = Message::built_in_controller_req_msg(Message::update_status_req_msg_content(
                input.key.namespace, input.key.name, new_daemon_set.marshal(), input.rest_id_allocator.allocate().1
            ));
            let s_prime = s;
            let output = BuiltinControllersActionOutput {
                send: Multiset::singleton(update_status_req_msg),
                rest_id_allocator: input.rest_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

}

}
