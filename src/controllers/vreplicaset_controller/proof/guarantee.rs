use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::helper_invariants,
    trusted::{
        rely_guarantee::*,
        spec_types::*, 
    },
};
use crate::vstd_ext::seq_lib::*;
use vstd::prelude::*;

verus! {

#[verifier(rlimit(50))]
pub proof fn guarantee_condition_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action (without weak fairness).
        spec.entails(always(lift_action(cluster.next()))),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vrs controller runs in the cluster.
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
        &&& local_pods_have_vrs_prefix(controller_id)(s_prime)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
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
            Step::ControllerStep((id, _, cr_key_opt)) => {
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
                        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());
                        if new_msgs.contains(msg) {
                            if msg.content.is_get_then_delete_request() {
                                let req = msg.content.get_get_then_delete_request();
                                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                                let next_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                                assert(has_vrs_prefix(req.key.name)) by {
                                    assert(next_state.reconcile_step is AfterDeletePod);
                                    let diff = next_state.reconcile_step->AfterDeletePod_0;
                                    assert(exists |i| #![trigger next_state.filtered_pods->0[i]] 0 <= i < next_state.filtered_pods->0.len() && req.key.name == next_state.filtered_pods->0[i].metadata.name->0) by {
                                        if state.reconcile_step is AfterListPods {
                                            assert(next_state.filtered_pods->0.len() > triggering_cr.spec.replicas.unwrap_or(1));
                                            assert(req.key.name == next_state.filtered_pods->0[next_state.filtered_pods->0.len() - triggering_cr.spec.replicas.unwrap_or(1)].metadata.name->0);
                                        } else {
                                            assume(false);
                                        }
                                    }
                                }
                                assert(req.owner_ref == triggering_cr.controller_owner_ref());
                            } else if msg.content.is_get_then_update_status_request() {
                                let req = msg.content.get_get_then_update_status_request();
                                assert(req.obj.kind == VReplicaSetView::kind());
                            } else if msg.content.is_create_request() {
                                let req = msg.content.get_create_request();
                                assert(has_vrs_prefix(req.obj.metadata.generate_name->0)) by {
                                    assert(req.obj.metadata.generate_name->0 == pod_generate_name(triggering_cr));
                                    let suffix = triggering_cr.metadata.name.unwrap() + "-"@;
                                    assert(req.obj.metadata.generate_name->0 == VReplicaSetView::kind()->CustomResourceKind_0 + "-"@ + suffix);
                                }
                                assert(req.obj == make_pod(triggering_cr).marshal());
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
    let requirements = |s: ClusterState, cr_key: ObjectRef| {
        let local_state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0;
        &&& local_state.filtered_pods is Some
        ==> forall |i| #![trigger local_state.filtered_pods->0[i]] 0 <= i < local_state.filtered_pods->0.len()
            ==> has_vrs_prefix(local_state.filtered_pods->0[i].metadata.name->0)
    };
    assert forall |s, s_prime| inv(s) && #[trigger] cluster.next()(s, s_prime) implies inv(s_prime) by {
        assert forall |cr_key| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(cr_key) && cr_key.kind == VReplicaSetView::kind()
            implies requirements(s_prime, cr_key) by {
                assume(false);
        }
    }
    init_invariant(spec, cluster.init(), cluster.next(), inv);
}

}
