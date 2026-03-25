use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::kubernetes_cluster::spec::api_server::{state_machine::*, types::InstalledTypes};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::helper_invariants,
    trusted::{
        rely_guarantee::*,
        spec_types::*,
        step::*,
    },
};
use crate::vstd_ext::{seq_lib::*, set_lib::*, map_lib::*};
use vstd::{prelude::*, map_lib::*};

verus! {

pub open spec fn local_pods_have_vrs_prefix(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |cr_key: ObjectRef| #[trigger] s.ongoing_reconciles(controller_id).contains_key(cr_key) && cr_key.kind == VReplicaSetView::kind()
            ==> {
            let local_state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0;
            &&& local_state.filtered_pods is Some
            ==> forall |i| #![trigger local_state.filtered_pods->0[i]] 0 <= i < local_state.filtered_pods->0.len()
                ==> has_vrs_prefix(local_state.filtered_pods->0[i].metadata.name->0)
        }
    }
}

proof fn lemma_always_local_pods_have_vrs_prefix(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
ensures
    spec.entails(always(lift_state(local_pods_have_vrs_prefix(controller_id)))),
{
    let inv = local_pods_have_vrs_prefix(controller_id);

    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_cr_states_are_unmarshallable::<VReplicaSetReconciler, VReplicaSetReconcileState, VReplicaSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_etcd_is_finite(spec);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::etcd_is_finite()(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::etcd_is_finite())
    );

    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |cr_key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(cr_key) && cr_key.kind == VReplicaSetView::kind()
            implies {
            let local_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0;
            &&& local_state.filtered_pods is Some
            ==> forall |i| #![trigger local_state.filtered_pods->0[i]] 0 <= i < local_state.filtered_pods->0.len()
                ==> has_vrs_prefix(local_state.filtered_pods->0[i].metadata.name->0)
        } by {
            if s.ongoing_reconciles(controller_id).contains_key(cr_key) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                let local_state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0;
                let next_local_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0;
                match step {
                    Step::ControllerStep((id, resp_msg_opt, cr_key_opt)) => {
                        if id == controller_id && cr_key_opt == Some(cr_key) {
                            VReplicaSetReconcileState::marshal_preserves_integrity();
                            VReplicaSetView::marshal_preserves_integrity();
                            PodView::marshal_preserves_integrity();
                            let vrs = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();

                            // The only time filtered_pods changes is AfterListPods step
                            match local_state.reconcile_step {
                                VReplicaSetRecStepView::AfterListPods => {
                                    if resp_msg_opt is Some {
                                        let resp_msg = resp_msg_opt->0;
                                        if is_some_k_list_resp_view(Some(ResponseView::KResponse(resp_msg.content->APIResponse_0)))
                                            && extract_some_k_list_resp_view(Some(ResponseView::KResponse(resp_msg.content->APIResponse_0))) is Ok {
                                            let objs = extract_some_k_list_resp_view(Some(ResponseView::KResponse(resp_msg.content->APIResponse_0))).unwrap();
                                            let pods_or_none = objects_to_pods(objs);
                                            if pods_or_none.is_some() {
                                                let pods = pods_or_none.unwrap();
                                                let filtered_pods = filter_pods(pods, vrs);
                                                let replicas = vrs.spec.replicas.unwrap_or(1);
                                                if replicas >= 0 && filtered_pods.len() > replicas {
                                                    // filtered_pods is set in the new state
                                                    // Each pod in filtered_pods passes pod_filter, which requires has_vrs_prefix
                                                    assert forall |i| #![trigger filtered_pods[i]] 0 <= i < filtered_pods.len()
                                                        implies has_vrs_prefix(filtered_pods[i].metadata.name->0) by {
                                                        assert(filtered_pods.contains(filtered_pods[i]));
                                                        seq_filter_contains_implies_seq_contains(pods, pod_filter(vrs), filtered_pods[i]);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                },
                                _ => {
                                    // In all other steps, filtered_pods is inherited unchanged via ..state
                                }
                            }
                        }
                    },
                    _ => {}
                }
            } else {
                // New reconcile: init state has filtered_pods = None, so implication is vacuously true
                VReplicaSetReconcileState::marshal_preserves_integrity();
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

#[verifier(rlimit(50))]
pub proof fn guarantee_condition_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
    ensures
        spec.entails(always(lift_state(vrs_guarantee(controller_id))))
{
    let invariant = vrs_guarantee(controller_id);

    cluster.lemma_always_cr_states_are_unmarshallable::<VReplicaSetReconciler, VReplicaSetReconcileState, VReplicaSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    lemma_always_local_pods_have_vrs_prefix(spec, cluster, controller_id);
    always_to_always_later(spec, lift_state(local_pods_have_vrs_prefix(controller_id)));

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& local_pods_have_vrs_prefix(controller_id)(s)
        &&& local_pods_have_vrs_prefix(controller_id)(s_prime)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(local_pods_have_vrs_prefix(controller_id)),
        later(lift_state(local_pods_have_vrs_prefix(controller_id)))
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        VReplicaSetView::marshal_preserves_integrity();
        VReplicaSetReconcileState::marshal_preserves_integrity();
        PodView::marshal_preserves_integrity();

        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(req_msg_opt) => {
                let req_msg = req_msg_opt.unwrap();

                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_guarantee_create_req(req)(s_prime),
                    APIRequest::GetThenDeleteRequest(req) => vrs_guarantee_get_then_delete_req(req)(s_prime),
                    APIRequest::GetThenUpdateStatusRequest(req) => vrs_guarantee_get_then_update_status_req(req),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
            Step::ControllerStep((id, resp_msg_opt, cr_key_opt)) => {
                let cr_key = cr_key_opt->0;
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_guarantee_create_req(req)(s_prime),
                    APIRequest::GetThenDeleteRequest(req) => vrs_guarantee_get_then_delete_req(req)(s_prime),
                    APIRequest::GetThenUpdateStatusRequest(req) => vrs_guarantee_get_then_update_status_req(req),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

                    if id == controller_id {
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());
                        if new_msgs.contains(msg) {
                            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();

                            if msg.content.is_create_request() {
                                let req = msg.content.get_create_request();
                                assert(has_vrs_prefix(req.obj.metadata.generate_name->0)) by {
                                    assert(req.obj.metadata.generate_name->0 == pod_generate_name(triggering_cr));
                                    let suffix = triggering_cr.metadata.name.unwrap() + "-"@;
                                    assert(req.obj.metadata.generate_name->0 == VReplicaSetView::kind()->CustomResourceKind_0 + "-"@ + suffix);
                                }
                                assert(req.obj == make_pod(triggering_cr).marshal());
                            } else if msg.content.is_get_then_delete_request() {
                                let req = msg.content.get_get_then_delete_request();
                                let next_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                                assert(next_state.reconcile_step is AfterDeletePod);
                                let diff = next_state.reconcile_step->AfterDeletePod_0 as int;

                                // The key insight: after transition, next_state.filtered_pods
                                // satisfies local_pods_have_vrs_prefix (from the s_prime invariant).
                                // The req.key.name comes from filtered_pods[some_index].metadata.name->0,
                                // so it has vrs prefix.
                                if state.reconcile_step is AfterListPods {
                                    if next_state.filtered_pods is None || next_state.filtered_pods->0.len() <= diff || next_state.filtered_pods->0[diff].metadata.name is None {
                                        assert(false);
                                    }
                                    assert(has_vrs_prefix(req.key.name)) by {
                                        assert(next_state.filtered_pods->0.len() > triggering_cr.spec.replicas.unwrap_or(1));
                                        // req.key.name = filtered_pods[filtered_pods.len() - desired_replicas - 1].metadata.name->0
                                        // and filtered_pods was set from filter_pods which checks has_vrs_prefix per pod_filter
                                        // Use s_prime invariant: local_pods_have_vrs_prefix
                                        assert(s_prime.ongoing_reconciles(controller_id).contains_key(cr_key));
                                    }
                                } else {
                                    // AfterDeletePod -> AfterDeletePod: filtered_pods inherited from state
                                    if state.filtered_pods.is_none() {
                                        assert(false);
                                    }
                                    assert(has_vrs_prefix(req.key.name)) by {
                                        // Use s_prime invariant: local_pods_have_vrs_prefix
                                        assert(s_prime.ongoing_reconciles(controller_id).contains_key(cr_key));
                                    }
                                }
                                assert(req.owner_ref == triggering_cr.controller_owner_ref());
                            } else if msg.content.is_get_then_update_status_request() {
                                let req = msg.content.get_get_then_update_status_request();
                                assert(req.obj.kind == VReplicaSetView::kind());
                            }
                        }
                    }
                }
            }
            _ => {
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_guarantee_create_req(req)(s_prime),
                    APIRequest::GetThenDeleteRequest(req) => vrs_guarantee_get_then_delete_req(req)(s_prime),
                    APIRequest::GetThenUpdateStatusRequest(req) => vrs_guarantee_get_then_update_status_req(req),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}

}
