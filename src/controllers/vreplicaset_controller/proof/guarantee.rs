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
            ==> local_pods_are_bound_to_vrs_with_key(controller_id, cr_key, s)
    }
}

pub open spec fn local_pods_are_bound_to_vrs_with_key_in_local_state(cr_key: ObjectRef, local_state: VReplicaSetReconcileState) -> bool {
    &&& local_state.filtered_pods is Some
    ==> forall |i| #![trigger local_state.filtered_pods->0[i]] 0 <= i < local_state.filtered_pods->0.len()
        ==> {
            let pod = local_state.filtered_pods->0[i];
            &&& has_vrs_prefix(pod.metadata.name->0)
            &&& pod.metadata.namespace == Some(cr_key.namespace)
            &&& pod.metadata.owner_references is Some
            &&& exists |owner_ref: OwnerReferenceView| {
                &&& pod.metadata.owner_references->0.contains(owner_ref)
                &&& owner_ref.controller is Some
                &&& owner_ref.controller->0
                &&& owner_ref.kind == VReplicaSetView::kind()
                &&& owner_ref.name == cr_key.name
            }
        }
}

pub open spec fn local_pods_are_bound_to_vrs_with_key(controller_id: int, cr_key: ObjectRef, s: ClusterState) -> bool {
    let local_state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0;
    local_pods_are_bound_to_vrs_with_key_in_local_state(cr_key, local_state)
}

pub proof fn lemma_always_local_pods_have_vrs_prefix(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
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
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))
    );

    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |cr_key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(cr_key) && cr_key.kind == VReplicaSetView::kind()
            implies local_pods_are_bound_to_vrs_with_key(controller_id, cr_key, s_prime) by {
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
                                                // vrs.object_ref() == cr_key from consistent key invariant
                                                assert(vrs.object_ref() == cr_key);

                                                // Prove properties for all branches where filtered_pods is stored
                                                assert forall |i| #![trigger filtered_pods[i]] 0 <= i < filtered_pods.len()
                                                    implies {
                                                        let pod = filtered_pods[i];
                                                        &&& has_vrs_prefix(pod.metadata.name->0)
                                                        &&& pod.metadata.namespace == Some(cr_key.namespace)
                                                        &&& pod.metadata.owner_references is Some
                                                        &&& exists |owner_ref: OwnerReferenceView| {
                                                            &&& pod.metadata.owner_references->0.contains(owner_ref)
                                                            &&& owner_ref.controller is Some
                                                            &&& owner_ref.controller->0
                                                            &&& owner_ref.kind == VReplicaSetView::kind()
                                                            &&& owner_ref.name == cr_key.name
                                                        }
                                                    } by {
                                                    assert(filtered_pods.contains(filtered_pods[i]));
                                                    seq_filter_contains_implies_seq_contains(pods, pod_filter(vrs), filtered_pods[i]);
                                                    // pod_filter ensures owner_references_contains(vrs.controller_owner_ref())
                                                    // which gives us owner_ref with kind=VReplicaSetView::kind() and name=vrs.metadata.name->0=cr_key.name
                                                    let pod = filtered_pods[i];
                                                    assert(pod.metadata.owner_references_contains(vrs.controller_owner_ref()));
                                                    // owner_references_contains means vrs.controller_owner_ref() is in the seq
                                                    let owner_ref = vrs.controller_owner_ref();
                                                    assert(owner_ref.controller == Some(true));
                                                    assert(owner_ref.kind == VReplicaSetView::kind());
                                                    assert(owner_ref.name == vrs.metadata.name->0);
                                                    assert(owner_ref.name == cr_key.name);
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
#[verifier(spinoff_prover)]
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
    lemma_always_local_pods_have_vrs_prefix(spec, cluster, controller_id);
    always_to_always_later(spec, lift_state(local_pods_have_vrs_prefix(controller_id)));

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)(s)
        &&& local_pods_have_vrs_prefix(controller_id)(s)
        &&& local_pods_have_vrs_prefix(controller_id)(s_prime)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)),
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
                                if state.reconcile_step is AfterListPods {
                                    if next_state.filtered_pods is None || next_state.filtered_pods->0.len() <= diff || next_state.filtered_pods->0[diff].metadata.name is None {
                                        assert(false);
                                    }
                                    assert(has_vrs_prefix(req.key.name)) by {
                                        assert(next_state.filtered_pods->0.len() > triggering_cr.spec.replicas.unwrap_or(1));
                                        assert(s_prime.ongoing_reconciles(controller_id).contains_key(cr_key));
                                    }
                                } else {
                                    if state.filtered_pods.is_none() {
                                        assert(false);
                                    }
                                    assert(has_vrs_prefix(req.key.name)) by {
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
