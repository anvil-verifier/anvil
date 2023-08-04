// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::{
    proof::{
        cluster, cluster_safety, controller_runtime, controller_runtime_eventual_safety,
        controller_runtime_liveness, controller_runtime_safety, kubernetes_api_liveness,
        kubernetes_api_safety,
    },
    spec::{
        cluster::*,
        controller::common::{controller_req_msg, ControllerActionInput<E>, ControllerStep},
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::*,
        kubernetes_api::state_machine::{
            handle_create_request, handle_get_request, handle_request, transition_by_etcd,
            update_is_noop,
        },
        message::*,
    },
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::zookeeper_controller::{
    common::*,
    proof::common::*,
    spec::{reconciler::*, zookeepercluster::*},
};
use vstd::prelude::*;

verus! {

spec fn is_in_flight_controller_request_msg(s: ClusterState, req_msg: Message) -> bool {
    &&& req_msg.src.is_CustomController()
    &&& req_msg.content.is_APIRequest()
    &&& s.message_in_flight(req_msg)
}

// We have to define some desired properties for controller requests.
// Our first goal is to show that they are not delete requests.
spec fn is_not_delete_request(req_msg: Message) -> bool {
    !req_msg.content.is_delete_request()
}

spec fn deletion_property(req_msg: Message) -> StatePred<ClusterState> {
    // The safety properties related to controller requests should be in the form:
    // controller_msg(msg) /\ in_flight(msg) ==> desired properties
    |s: ClusterState| {
        is_in_flight_controller_request_msg(s, req_msg)
        ==> is_not_delete_request(req_msg)
    }
}

spec fn always_deletion_safety(req_msg: Message) -> TempPred<ClusterState> {
    always(lift_state(deletion_property(req_msg)))
}

proof fn deletion_safety_proof_forall_msg()
    ensures
        forall |msg: Message| cluster_spec().entails(#[trigger] always_deletion_safety(msg)),
{
    assert forall |req_msg: Message| cluster_spec().entails(#[trigger] always_deletion_safety(req_msg)) by {
        deletion_safety_proof(req_msg);
    }
}

proof fn deletion_safety_proof(req_msg: Message)
    ensures
        cluster_spec().entails(always_deletion_safety(req_msg)),
{
    init_invariant(
        cluster_spec(),
        ClusterProof::init(),
        ClusterProof::next(),
        deletion_property(req_msg)
    );
}

}
