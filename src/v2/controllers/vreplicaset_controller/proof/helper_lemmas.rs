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

#[verifier(external_body)]
pub proof fn lemma_filtered_pods_set_equals_matching_pods(
    s: ClusterState, vrs: VReplicaSetView, cluster: Cluster, 
    controller_id: int, resp_msg: Message
)
    requires
        //cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(vrs.object_ref())))),
        resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s),
        // Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        // cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        // cluster.each_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        // cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        // helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s),
        // helper_invariants::no_pending_update_or_update_status_request_on_pods()(s),
        // helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s),
        // helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, controller_id)(s),
        // helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)(s),
        // forall |diff: usize| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterCreatePod(diff))(s)),
        // forall |diff: usize| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterDeletePod(diff))(s)),
        // forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
        //     ==> #[trigger] vrs_not_interfered_by(other_id)(s)
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
    
    assert(objs.no_duplicates());

    assert forall |i: int, j: int| #![auto] 
        0 <= i && i < pods.len() && (0 <= j && j < pods.len()) && !(i == j)
        && pre
        implies !(pods.index(i) == pods.index(j)) by {
        
        // assert(pods_or_none == objects_to_pods(objs));
        // assert(pods_or_none.is_Some());
        //assert(objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0);
        assert(pods == objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()));
        PodView::marshal_preserves_integrity();
        assert(pods[i] == PodView::unmarshal(objs[i]).unwrap());
        assert(pods[j] == PodView::unmarshal(objs[j]).unwrap());
        assert(pods[i].marshal() == objs[i]);
        assert(pods[j].marshal() == objs[j]);
        assert(!(objs[i] == objs[j]));
        
        //assume(false);
    }

//     // First operation -- conversion from DynamicObjectView to PodView
//     let pods_as_dov_set = Set::new(|o: DynamicObjectView| {
//         let pod_or_error = PodView::unmarshal(o);
//         &&& PodView::unmarshal(o).is_Ok() 
//         &&& pods.contains(pod_or_error.unwrap())
//     });
//     assert(objs.to_set() == pods_as_dov_set);

//     // Second operation -- filtered out.


//     //assert(objs.to_set().subset_of(s.resources().values()));
//     assert({&&& matching_pod_entries(vrs, s.resources()).values().subset_of(objs.to_set())
//            &&& objects_to_pods(objs).is_Some()});

    assert(pods.no_duplicates());
    assert(filtered_pods.to_set().subset_of(pods.to_set()));
    assert(filtered_pods.no_duplicates());
    assert(filtered_pods.len() == matching_pod_entries(vrs, s.resources()).len());

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