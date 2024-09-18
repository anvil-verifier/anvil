// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::predicate::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use crate::v_replica_set_controller::{
    proof::{predicate::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub proof fn lemma_eventually_always_no_pending_update_or_update_status_request_on_pods(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView
)
    requires
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::pod_event_disabled()))),
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::desired_state_is(vrs)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_update_or_update_status_request_on_pods())))),
{
    let requirements = |msg: VRSMessage, s: VRSCluster| {
        &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != PodView::kind()
        &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != PodView::kind()
    };

    let stronger_next = |s: VRSCluster, s_prime: VRSCluster| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::desired_state_is(vrs)(s)
        &&& VRSCluster::each_object_in_etcd_is_well_formed()(s)
        &&& VRSCluster::pod_event_disabled()(s)
    };

    assert forall |s: VRSCluster, s_prime: VRSCluster| #[trigger]  #[trigger] stronger_next(s, s_prime) implies VRSCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: VRSMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.in_flight().contains(msg) {
                assert(requirements(msg, s));
                assert(requirements(msg, s_prime));
            } else {
                let step = choose |step| VRSCluster::next_step(s, s_prime, step);
                match step {
                    _ => {
                        assert(requirements(msg, s_prime));
                    }
                }
            }
        }
    }

    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(VRSCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(VRSCluster::next()), 
        lift_state(VRSCluster::desired_state_is(vrs)),
        lift_state(VRSCluster::each_object_in_etcd_is_well_formed()),
        lift_state(VRSCluster::pod_event_disabled())
    );

    VRSCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lift_state(VRSCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

}
