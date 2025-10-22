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
    trusted::{
        liveness_theorem::*, 
        rely_guarantee::*,
        spec_types::*, 
        step::*
    },
    proof::{helper_invariants, predicate::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*};
use vstd::{seq_lib::*, map_lib::*, seq::*};
use vstd::prelude::*;

verus! {

pub proof fn vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    ensures
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))))
        <==>
            spec.entails(always(lifted_vrs_rely_condition(cluster, controller_id))),
{
    let lhs = 
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))));
    let rhs = spec.entails(always(lifted_vrs_rely_condition(cluster, controller_id)));

    assert_by(
        lhs ==> rhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                lhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies vrs_rely(other_id)(ex.suffix(n).head()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lift_state(vrs_rely(other_id))))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lift_state(vrs_rely(other_id))))));
                assert(spec.implies(always(lift_state(vrs_rely(other_id)))).satisfied_by(ex));
                assert(always(lift_state(vrs_rely(other_id))).satisfied_by(ex));
                assert(lift_state(vrs_rely(other_id)).satisfied_by(ex.suffix(n)));
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
                implies vrs_rely(other_id)(ex.suffix(n).head()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lifted_vrs_rely_condition(cluster, controller_id)))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lifted_vrs_rely_condition(cluster, controller_id)))));
                assert(spec.implies(always(lifted_vrs_rely_condition(cluster, controller_id))).satisfied_by(ex));
                assert(always(lifted_vrs_rely_condition(cluster, controller_id)).satisfied_by(ex));
                assert(lifted_vrs_rely_condition(cluster, controller_id).satisfied_by(ex.suffix(n)));
            }
        }
    );
}

pub proof fn vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition_action(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    ensures
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))))
        <==>
            spec.entails(always(lifted_vrs_rely_condition_action(cluster, controller_id))),
{
    let lhs = 
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))));
    let rhs = spec.entails(always(lifted_vrs_rely_condition_action(cluster, controller_id)));

    assert_by(
        lhs ==> rhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                lhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies 
                vrs_rely(other_id)(ex.suffix(n).head())
                && vrs_rely(other_id)(ex.suffix(n).head_next()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lift_state(vrs_rely(other_id))))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lift_state(vrs_rely(other_id))))));
                assert(spec.implies(always(lift_state(vrs_rely(other_id)))).satisfied_by(ex));
                assert(always(lift_state(vrs_rely(other_id))).satisfied_by(ex));
                assert(lift_state(vrs_rely(other_id)).satisfied_by(ex.suffix(n)));
                assert(lift_state(vrs_rely(other_id)).satisfied_by(ex.suffix(n + 1)));
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
                vrs_rely(other_id)(ex.suffix(n).head())
                && vrs_rely(other_id)(ex.suffix(n).head_next()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lifted_vrs_rely_condition_action(cluster, controller_id)))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lifted_vrs_rely_condition_action(cluster, controller_id)))));
                assert(spec.implies(always(lifted_vrs_rely_condition_action(cluster, controller_id))).satisfied_by(ex));
                assert(always(lifted_vrs_rely_condition_action(cluster, controller_id)).satisfied_by(ex));
                assert(lifted_vrs_rely_condition_action(cluster, controller_id).satisfied_by(ex.suffix(n)));
                assert(lifted_vrs_rely_condition_action(cluster, controller_id).satisfied_by(ex.suffix(n + 1)));
            }
        }
    );
}

pub proof fn only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself_action(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    ensures
        spec.entails(always(tla_forall(|vrs: VReplicaSetView| 
            lift_state(helper_invariants::vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)))))
        <==>
            spec.entails(always(lifted_vrs_reconcile_request_only_interferes_with_itself_action(controller_id)))
{
    let lhs = 
        spec.entails(always(tla_forall(|vrs: VReplicaSetView| 
            lift_state(helper_invariants::vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)))));
    let rhs = spec.entails(always(lifted_vrs_reconcile_request_only_interferes_with_itself_action(controller_id)));

    assert_by(
        lhs ==> rhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, vrs: VReplicaSetView| #![auto]
                lhs
                && spec.satisfied_by(ex)
                implies 
                helper_invariants::vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)(ex.suffix(n).head())
                && helper_invariants::vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)(ex.suffix(n).head_next()) by {
                // Gradually unwrap the semantics of lhs
                // until Verus can show the consequent.
                let tla_forall_body = |vrs: VReplicaSetView| 
                    lift_state(helper_invariants::vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs));

                assert(valid(spec.implies(always(tla_forall(tla_forall_body)))));
                assert(spec.implies(always(tla_forall(tla_forall_body))).satisfied_by(ex));
                assert(always(tla_forall(tla_forall_body)).satisfied_by(ex));

                assert(tla_forall(tla_forall_body).satisfied_by(ex.suffix(n)));
                assert(tla_forall(tla_forall_body).satisfied_by(ex.suffix(n + 1)));

                assert(tla_forall_body(vrs).satisfied_by(ex.suffix(n)));
                assert(tla_forall_body(vrs).satisfied_by(ex.suffix(n + 1)));
            }
        }
    );
    
    assert_by(
        rhs ==> lhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, vrs: VReplicaSetView| #![auto]
                rhs
                && spec.satisfied_by(ex)
                implies 
                helper_invariants::vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)(ex.suffix(n).head())
                && helper_invariants::vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)(ex.suffix(n).head_next()) by {
                // Gradually unwrap the semantics of rhs
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lifted_vrs_reconcile_request_only_interferes_with_itself_action(controller_id)))));
                assert(spec.implies(always(lifted_vrs_reconcile_request_only_interferes_with_itself_action(controller_id))).satisfied_by(ex));
                assert(always(lifted_vrs_reconcile_request_only_interferes_with_itself_action(controller_id)).satisfied_by(ex));
                
                assert(lifted_vrs_reconcile_request_only_interferes_with_itself_action(controller_id).satisfied_by(ex.suffix(n)));
                assert(lifted_vrs_reconcile_request_only_interferes_with_itself_action(controller_id).satisfied_by(ex.suffix(n + 1)));

            }
        }
    );
}

pub proof fn matching_pods_equal_to_matching_pod_entries_values(vrs: VReplicaSetView, s: StoredState)
    ensures
        matching_pods(vrs, s) =~= matching_pod_entries(vrs, s).values()
{
    assert forall |o: DynamicObjectView| #[trigger] matching_pods(vrs, s).contains(o)
        implies matching_pod_entries(vrs, s).values().contains(o) by {
        assert(s.values().contains(o));
        let key = choose |key: ObjectRef| s.contains_key(key) && #[trigger] s[key] == o;
        assert(matching_pod_entries(vrs, s).contains_key(key) && matching_pod_entries(vrs, s)[key] == o);
    }
}

pub proof fn lemma_filtered_pods_set_equals_matching_pods(
    s: ClusterState, vrs: VReplicaSetView, cluster: Cluster, 
    controller_id: int, resp_msg: Message
)
    requires
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        Cluster::etcd_is_finite()(s),
        resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s),
        forall |obj: DynamicObjectView| #[trigger] matching_pods(vrs, s.resources()).contains(obj) ==> PodView::unmarshal(obj) is Ok,
    ensures
        ({
            let resp_objs = resp_msg.content.get_list_response().res.unwrap();
            let filtered_pods = filter_pods(objects_to_pods(resp_objs).unwrap(), vrs);
            let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
            &&& filtered_pods.no_duplicates()
            &&& filtered_pods.len() == matching_pods(vrs, s.resources()).len()
            &&& filtered_pods.to_set() == matching_pods(vrs, s.resources()).map(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0)
            &&& filtered_pod_keys.no_duplicates()
        }),
{
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let resp_obj_keys = resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref());
    let resp_pods = objects_to_pods(resp_objs).unwrap();
    let filtered_objs = resp_objs.filter(|obj| owned_selector_match_is(vrs, obj));
    let filtered_pods = filter_pods(objects_to_pods(resp_objs).unwrap(), vrs);
    let filter_pods_pred = |pod: PodView| 
        pod.metadata.owner_references_contains(vrs.controller_owner_ref())
        && vrs.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
        && pod.metadata.deletion_timestamp is None;
    assert(filtered_pods.no_duplicates()) by {
        assert(objects_to_pods(resp_objs).unwrap().no_duplicates());
        seq_filter_preserves_no_duplicates(objects_to_pods(resp_objs).unwrap(), filter_pods_pred);
    }
    assert(filtered_pods == objects_to_pods(resp_objs).unwrap().filter(filter_pods_pred));
    PodView::marshal_preserves_integrity();
    // get rid of s.resources
    // now we only need to prove
    // resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)) == 
    // filter_pods(objects_to_pods(resp_objs).unwrap(), vrs).map_values(|p: PodView| p.marshal())
    assert(matching_pods(vrs, s.resources()) == filtered_objs.to_set());
    filtered_objs.lemma_to_set_map_commutes(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0);
    assert(matching_pods(vrs, s.resources()).map(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0) == filtered_objs.map_values(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0).to_set());
    assert(filtered_objs.map_values(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0) == filtered_pods) by {
        // get rid of objects_to_pods
        true_pred_on_all_element_equal_to_pred_on_all_index(resp_objs, |obj: DynamicObjectView| PodView::unmarshal(obj) is Ok);
        assert(forall |i: int| 0 <= i < resp_objs.len() ==> #[trigger] resp_objs[i].kind == PodView::kind() && PodView::unmarshal(resp_objs[i]) is Ok);
        PodView::marshal_preserves_integrity();
        PodView::marshal_preserves_metadata();
        assert(resp_pods.len() == resp_objs.len());
        // prove 2 filters are equal
        true_pred_on_all_element_equal_to_pred_on_all_index(resp_objs, |obj: DynamicObjectView| obj.metadata.namespace == vrs.metadata.namespace);
        assert(forall |i: int| 0 <= i < resp_objs.len() ==> {
            &&& #[trigger] resp_objs[i].kind == PodView::kind()
            &&& #[trigger] resp_objs[i].metadata.namespace is Some
            &&& #[trigger] resp_objs[i].metadata.namespace == vrs.metadata.namespace
        });
        assert(forall |i: int| 0 <= i < resp_objs.len() ==>
            #[trigger] owned_selector_match_is(vrs, resp_objs[i]) == #[trigger] filter_pods_pred(resp_pods[i]));
        PodView::unmarshal_result_determined_by_unmarshal_spec_and_status();
        assert(filtered_objs.map_values(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0) =~= filtered_pods) by {
            assert forall |i: int| 0 <= i < resp_objs.len() implies #[trigger] resp_pods[i] == resp_objs.map_values(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0)[i] by {
                // spec and status are encoded nestedly
                assert(PodView::unmarshal(resp_objs[i]) is Ok);
                assert(PodView::unmarshal(resp_objs[i])->Ok_0 == resp_pods[i]);
            }
            assert(resp_pods.filter(filter_pods_pred) == filtered_objs.map_values(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0)) by {
                commutativity_of_seq_map_and_filter(resp_objs, |obj: DynamicObjectView| owned_selector_match_is(vrs, obj), filter_pods_pred, |obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0);
            }
            assert(filtered_objs.len() == filtered_pods.len());
            assert forall |i: int| 0 <= i < filtered_pods.len() implies filtered_pods[i] == filtered_objs.map_values(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0)[i] by {
                assert(filtered_pods == resp_pods.filter(filter_pods_pred));
                assert(PodView::unmarshal(filtered_objs[i]) is Ok) by {
                    assert(forall |obj: DynamicObjectView| #[trigger] filtered_objs.contains(obj) ==> PodView::unmarshal(obj) is Ok) by {
                        true_pred_on_seq_implies_true_pred_on_filtered_seq(resp_objs, |obj: DynamicObjectView| PodView::unmarshal(obj) is Ok, |obj: DynamicObjectView| owned_selector_match_is(vrs, obj));
                    }
                    true_pred_on_all_element_equal_to_pred_on_all_index(filtered_objs, |obj: DynamicObjectView| PodView::unmarshal(obj) is Ok);
                }
                assert(PodView::unmarshal(filtered_objs[i])->Ok_0 == filtered_pods[i]);
            }
            assert(filtered_pods.len() == filtered_pods.map_values(|p: PodView| p.marshal()).len());
            assert_seqs_equal!(filtered_pods, filtered_objs.map_values(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0));
        }
    }
    assert(filtered_pods.len() == matching_pods(vrs, s.resources()).len()) by {
        assert(matching_pods(vrs, s.resources()) == filtered_objs.to_set());
        assert(resp_objs.no_duplicates());
        seq_filter_preserves_no_duplicates(resp_objs, |obj| owned_selector_match_is(vrs, obj));
        assert(filtered_objs.no_duplicates());
        filtered_objs.unique_seq_to_set();
        assert(matching_pods(vrs, s.resources()).len() == filtered_objs.len());
        assert(filtered_objs.map_values(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0) == filtered_pods);
        assert(filtered_objs.map_values(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0).len() == filtered_pods.len());
        assert(filtered_pods.len() == filtered_pods.len());
    }
    let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
    assert forall |i: int, j: int| #![auto]
        0 <= i < filtered_pod_keys.len()
        && 0 <= j < filtered_pod_keys.len()
        && i != j
        && filtered_pods.no_duplicates()
        implies filtered_pod_keys[i] != filtered_pod_keys[j] by {

        seq_filter_contains_implies_seq_contains(
            resp_pods,
            |pod: PodView|
                pod.metadata.owner_references_contains(vrs.controller_owner_ref())
                && vrs.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                && pod.metadata.deletion_timestamp is None,
            filtered_pods[i]
        );
        seq_filter_contains_implies_seq_contains(
            resp_pods,
            |pod: PodView|
                pod.metadata.owner_references_contains(vrs.controller_owner_ref())
                && vrs.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                && pod.metadata.deletion_timestamp is None,
            filtered_pods[j]
        );

        let idxi = choose |idx| 0 <= idx < resp_pods.len() && resp_pods[idx] == filtered_pods[i];
        let idxj = choose |idx| 0 <= idx < resp_pods.len() && resp_pods[idx] == filtered_pods[j];

        assert(resp_pods == resp_objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()));
        assert(resp_pods.len() == resp_objs.len());
        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
            resp_objs,
            |obj: DynamicObjectView| PodView::unmarshal(obj).is_err()
        );
        assert(resp_objs.contains(resp_objs[idxi]));
        assert(resp_objs.contains(resp_objs[idxj]));
        assert(PodView::unmarshal(resp_objs[idxi]) is Ok);
        assert(PodView::unmarshal(resp_objs[idxj]) is Ok);

        assert(resp_pods[idxi] == PodView::unmarshal(resp_objs[idxi])->Ok_0);
        assert(resp_pods[idxj] == PodView::unmarshal(resp_objs[idxj])->Ok_0);

        assert(resp_pods[idxi].object_ref() == resp_objs[idxi].object_ref());
        assert(resp_pods[idxj].object_ref() == resp_objs[idxj].object_ref());

        if idxi == idxj {
            seq_filter_preserves_no_duplicates(
                resp_pods,
                |pod: PodView|
                    pod.metadata.owner_references_contains(vrs.controller_owner_ref())
                    && vrs.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                    && pod.metadata.deletion_timestamp is None,
            );
        } else {
            assert(resp_obj_keys[idxi] == resp_objs[idxi].object_ref());
            assert(resp_obj_keys[idxj] == resp_objs[idxj].object_ref());
            assert(resp_objs[idxi].object_ref() != resp_objs[idxj].object_ref());
        }
    }
}

}
