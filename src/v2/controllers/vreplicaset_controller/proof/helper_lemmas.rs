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
use vstd::seq_lib::*;
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
    ensures
        ({
            let resp_objs = resp_msg.content.get_list_response().res.unwrap();
            let filtered_pods = filter_pods(objects_to_pods(resp_objs).unwrap(), vrs);
            &&& filtered_pods.no_duplicates()
            &&& filtered_pods.len() == matching_pod_entries(vrs, s.resources()).len() == matching_pods(vrs, s.resources()).len()
            &&& filtered_pods.map_values(|p: PodView| p.marshal()).to_set() == matching_pod_entries(vrs, s.resources()).values()
        }),
{
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let filtered_pods = filter_pods(objects_to_pods(resp_objs).unwrap(), vrs);
    let filter_pods_pred = |pod: PodView| 
        pod.metadata.owner_references_contains(vrs.controller_owner_ref())
        && vrs.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
        && pod.metadata.deletion_timestamp.is_None();
    assert(filtered_pods.no_duplicates()) by {
        assert(objects_to_pods(resp_objs).unwrap().no_duplicates());
        seq_filter_preserves_no_duplicates(objects_to_pods(resp_objs).unwrap(), filter_pods_pred);
        assert(filtered_pods == objects_to_pods(resp_objs).unwrap().filter(filter_pods_pred));
    }
    PodView::marshal_preserves_integrity();
    // get rid of s.resources
    // now we only need to prove
    // resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)) == 
    // filter_pods(objects_to_pods(resp_objs).unwrap(), vrs).map_values(|p: PodView| p.marshal())
    assert(matching_pod_entries(vrs, s.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set());
    assert(resp_objs.filter(|obj: DynamicObjectView| owned_selector_match_is(vrs, obj)) == filter_pods(objects_to_pods(resp_objs).unwrap(), vrs).map_values(|p: PodView| p.marshal())) by {
        // get rid of objects_to_pods
        true_pred_on_all_element_equal_to_pred_on_all_index(resp_objs, |obj: DynamicObjectView| PodView::unmarshal(obj).is_Ok());
        assert(forall |i: int| 0 <= i < resp_objs.len() ==> #[trigger] resp_objs[i].kind == PodView::kind() && PodView::unmarshal(resp_objs[i]).is_Ok());
        PodView::marshal_preserves_integrity();
        PodView::marshal_preserves_metadata();
        let resp_pods = objects_to_pods(resp_objs).unwrap();
        assert(resp_pods.len() == resp_objs.len());
        // prove 2 filters are equal
        true_pred_on_all_element_equal_to_pred_on_all_index(resp_objs, |obj: DynamicObjectView| obj.metadata.namespace == vrs.metadata.namespace);
        assert(forall |i: int| 0 <= i < resp_objs.len() ==> {
            &&& #[trigger] resp_objs[i].kind == PodView::kind()
            &&& #[trigger] resp_objs[i].metadata.namespace.is_Some()
            &&& #[trigger] resp_objs[i].metadata.namespace == vrs.metadata.namespace
        });
        assert(forall |i: int| 0 <= i < resp_objs.len() ==>
            #[trigger] owned_selector_match_is(vrs, resp_objs[i]) == #[trigger] filter_pods_pred(resp_pods[i]));
        PodView::unmarshal_result_determined_by_unmarshal_spec_and_status();
        let filtered_pods = filter_pods(objects_to_pods(resp_objs).unwrap(), vrs);
        let filtered_objs = resp_objs.filter(|obj| owned_selector_match_is(vrs, obj));
        assert(filtered_objs =~= filtered_pods.map_values(|p: PodView| p.marshal())) by {
            assert forall |i: int| 0 <= i < resp_objs.len() implies #[trigger] resp_pods[i].marshal() == resp_objs[i] by {
                // spec and status are encoded nestedly
                assert(PodView::unmarshal(resp_objs[i]).is_Ok());
                assert(PodView::unmarshal(resp_objs[i]).get_Ok_0() == resp_pods[i]);
                unmarshal_preserves_integrity(resp_pods[i], resp_objs[i]);
            }
            assert(resp_pods.filter(filter_pods_pred) == filtered_objs.map_values(|obj: DynamicObjectView| PodView::unmarshal(obj).get_Ok_0())) by {
                commutativity_of_seq_map_and_filter(resp_objs, |obj: DynamicObjectView| owned_selector_match_is(vrs, obj), filter_pods_pred, |obj: DynamicObjectView| PodView::unmarshal(obj).get_Ok_0());
            }
            assert(filtered_objs.len() == filtered_pods.len());
            assert forall |i: int| 0 <= i < filtered_pods.len() implies filtered_pods.map_values(|p: PodView| p.marshal())[i] == filtered_objs[i] by {
                assert(filtered_pods == resp_pods.filter(filter_pods_pred));
                assert(PodView::unmarshal(filtered_objs[i]).is_Ok()) by {
                    assert(forall |obj: DynamicObjectView| #[trigger] filtered_objs.contains(obj) ==> PodView::unmarshal(obj).is_Ok()) by {
                        true_pred_on_seq_implies_true_pred_on_filtered_seq(resp_objs, |obj: DynamicObjectView| PodView::unmarshal(obj).is_Ok(), |obj: DynamicObjectView| owned_selector_match_is(vrs, obj));
                    }
                    true_pred_on_all_element_equal_to_pred_on_all_index(filtered_objs, |obj: DynamicObjectView| PodView::unmarshal(obj).is_Ok());
                }
                assert(PodView::unmarshal(filtered_objs[i]).get_Ok_0() == filtered_pods[i]);
                unmarshal_preserves_integrity(filtered_pods[i], filtered_objs[i]);
            }
            assert(filtered_pods.len() == filtered_pods.map_values(|p: PodView| p.marshal()).len());
            assert_seqs_equal!(filtered_pods.map_values(|p: PodView| p.marshal()), filtered_objs);
        }
    }
}

#[verifier(external_body)]
pub proof fn unmarshal_preserves_integrity(pod: PodView, obj: DynamicObjectView)
    requires PodView::unmarshal(obj).is_Ok() && #[trigger] PodView::unmarshal(obj).get_Ok_0() == pod,
    ensures pod.marshal() == obj;

}