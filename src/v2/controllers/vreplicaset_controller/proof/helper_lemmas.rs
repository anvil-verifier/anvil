// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
    proof::{helper_invariants, predicate::*},
};
use crate::vstd_ext::seq_lib::*;
use vstd::prelude::*;

verus! {

pub proof fn vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    ensures
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))))
        <==>
            spec.entails(always(lifted_vrs_non_interference_property(cluster, controller_id))),
{
    let lhs = 
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))));
    let rhs = spec.entails(always(lifted_vrs_non_interference_property(cluster, controller_id)));

    assert_by(
        lhs ==> rhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                lhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies vrs_not_interfered_by(other_id)(ex.suffix(n).head()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lift_state(vrs_not_interfered_by(other_id))))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lift_state(vrs_not_interfered_by(other_id))))));
                assert(spec.implies(always(lift_state(vrs_not_interfered_by(other_id)))).satisfied_by(ex));
                assert(always(lift_state(vrs_not_interfered_by(other_id))).satisfied_by(ex));
                assert(lift_state(vrs_not_interfered_by(other_id)).satisfied_by(ex.suffix(n)));
            }
        }
    );
    
    assert_by(
        rhs ==> lhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                rhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies vrs_not_interfered_by(other_id)(ex.suffix(n).head()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lifted_vrs_non_interference_property(cluster, controller_id)))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lifted_vrs_non_interference_property(cluster, controller_id)))));
                assert(spec.implies(always(lifted_vrs_non_interference_property(cluster, controller_id))).satisfied_by(ex));
                assert(always(lifted_vrs_non_interference_property(cluster, controller_id)).satisfied_by(ex));
                assert(lifted_vrs_non_interference_property(cluster, controller_id).satisfied_by(ex.suffix(n)));
            }
        }
    );
}

// TODO: Prove this lemma.
// Annoying sequence reasoning.
#[verifier(external_body)]
pub proof fn lemma_filtered_pods_set_equals_matching_pods(
    s: ClusterState, vrs: VReplicaSetView, cluster: Cluster, 
    controller_id: int, resp_msg: Message
)
    requires
        resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s),
    ensures
        ({
            let objs = resp_msg.content.get_list_response().res.unwrap();
            let pods_or_none = objects_to_pods(objs);
            let pods = pods_or_none.unwrap();
            let filtered_pods = filter_pods(pods, vrs);
            &&& filtered_pods.no_duplicates()
            &&& filtered_pods.len() == matching_pod_entries(vrs, s.resources()).len()
            &&& filtered_pods.map_values(|p: PodView| p.marshal()).to_set() == matching_pod_entries(vrs, s.resources()).values()
        }),
{
    let pre = resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s);
    let objs = resp_msg.content.get_list_response().res.unwrap();
    let pods_or_none = objects_to_pods(objs);
    let pods = pods_or_none.unwrap();
    let filtered_pods = filter_pods(pods, vrs);

    assert(pods.no_duplicates());
    let pred = |pod: PodView|
        pod.metadata.owner_references_contains(vrs.controller_owner_ref())
        && vrs.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
        && pod.metadata.deletion_timestamp.is_None();
    seq_filter_preserves_no_duplicates(pods, pred);
    assert(filtered_pods.no_duplicates());
    
    assert(filtered_pods.len() == matching_pod_entries(vrs, s.resources()).len());
    assume(filtered_pods.map_values(|p: PodView| p.marshal()).to_set() == matching_pod_entries(vrs, s.resources()).values());

    // let filtered_pods_set = filtered_pods.map_values(|p: PodView| p.marshal()).to_set();
    // let matching_pods_set = matching_pod_entries(vrs, s.resources()).values();
    // assert forall |o: DynamicObjectView| #[trigger] filtered_pods_set.contains(o) implies matching_pods_set.contains(o) by {
    //     //assume(false);
    // } 
    // assert forall |o: DynamicObjectView| #[trigger] matching_pods_set.contains(o) implies filtered_pods_set.contains(o) by {
    //     //assume(false);
    // } 
}

}