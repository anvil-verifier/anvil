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

pub proof fn vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    ensures
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))))
        <==>
            spec.entails(always(lifted_vrs_non_interference_property_action(cluster, controller_id))),
{
    let lhs = 
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))));
    let rhs = spec.entails(always(lifted_vrs_non_interference_property_action(cluster, controller_id)));

    assert_by(
        lhs ==> rhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                lhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies 
                vrs_not_interfered_by(other_id)(ex.suffix(n).head())
                && vrs_not_interfered_by(other_id)(ex.suffix(n).head_next()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lift_state(vrs_not_interfered_by(other_id))))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lift_state(vrs_not_interfered_by(other_id))))));
                assert(spec.implies(always(lift_state(vrs_not_interfered_by(other_id)))).satisfied_by(ex));
                assert(always(lift_state(vrs_not_interfered_by(other_id))).satisfied_by(ex));
                assert(lift_state(vrs_not_interfered_by(other_id)).satisfied_by(ex.suffix(n)));
                assert(lift_state(vrs_not_interfered_by(other_id)).satisfied_by(ex.suffix(n + 1)));
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
                implies 
                vrs_not_interfered_by(other_id)(ex.suffix(n).head())
                && vrs_not_interfered_by(other_id)(ex.suffix(n).head_next()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lifted_vrs_non_interference_property_action(cluster, controller_id)))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lifted_vrs_non_interference_property_action(cluster, controller_id)))));
                assert(spec.implies(always(lifted_vrs_non_interference_property_action(cluster, controller_id))).satisfied_by(ex));
                assert(always(lifted_vrs_non_interference_property_action(cluster, controller_id)).satisfied_by(ex));
                assert(lifted_vrs_non_interference_property_action(cluster, controller_id).satisfied_by(ex.suffix(n)));
                assert(lifted_vrs_non_interference_property_action(cluster, controller_id).satisfied_by(ex.suffix(n + 1)));
            }
        }
    );
}

// TODO: Prove this lemma.
// More comments sketching an informal proof in the body.
pub proof fn lemma_filtered_pods_set_equals_matching_pods(
    s: ClusterState, vrs: VReplicaSetView, cluster: Cluster, 
    controller_id: int, resp_msg: Message
)
    requires
        resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s),
        list_pod_resp_contains_all_namespaced_pods(vrs, controller_id, resp_msg)(s),
    ensures
        ({
            let objs = resp_msg.content.get_list_response().res.unwrap();
            let pods_or_none = objects_to_pods(objs);
            let pods = pods_or_none.unwrap();
            let filtered_pods = filter_pods(pods, vrs);
            &&& filtered_pods.no_duplicates()
            &&& filtered_pods.len() == matching_pods(vrs, s.resources()).len()
            &&& filtered_pods.map_values(|p: PodView| p.marshal()).to_set() == matching_pod_entries(vrs, s.resources()).values()
        }),
{
    let pre = resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s);
    let objs = resp_msg.content.get_list_response().res.unwrap();
    let pods_or_none = objects_to_pods(objs);
    let pods = pods_or_none.unwrap();
    let filtered_pods = filter_pods(pods, vrs);

    // We've proved the first property of filtered_pods.
    assert(pods.no_duplicates());
    let pred = |pod: PodView|
        pod.metadata.owner_references_contains(vrs.controller_owner_ref())
        && vrs.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
        && pod.metadata.deletion_timestamp.is_None();
    seq_filter_preserves_no_duplicates(pods, pred);
    assert(filtered_pods.no_duplicates());
    
    // We now must prove that the number of elements of `filtered_pods` is equal to the number
    // of matching pods. This is true by the way we construct `filtered_pods`.
    assert(filtered_pods.len() == matching_pods(vrs, s.resources()).len());

    // We now must prove that the elements of `filtered_pods` are precisely the matching pod
    // entries. This is also true by construction.
    assert(filtered_pods.map_values(|p: PodView| p.marshal()).to_set() == matching_pod_entries(vrs, s.resources()).values());
}

// should we put it in trusted?
// or in API related lemmas
// and remove the vrs-related part of code
pub open spec fn list_pod_resp_contains_all_namespaced_pods(
    vrs: VReplicaSetView, 
    controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let objs = resp_msg.content.get_list_response().res.unwrap();
        let pods_or_none = objects_to_pods(objs);
        let pods = pods_or_none.unwrap();
        let objs_in_s = s.resources().values().to_seq();
        let pods_or_none_in_s = objects_to_pods(objs_in_s);
        let pods_in_s = pods_or_none_in_s.unwrap();
        // ns is consistent
        &&& forall |p: PodView| pods.contains(p) ==> p.metadata.namespace.unwrap() == vrs.metadata.namespace.unwrap()
        &&& pods_in_s == pods
        }
    }
}