use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::helper_invariants,
    trusted::{
        rely_guarantee::*,
        spec_types::*, 
    },
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vstd_ext::seq_lib::*;
use vstd::prelude::*;

verus! {

// TODO: finish proof; proof in progress.
#[verifier(external_body)]
#[verifier(rlimit(100))]
pub proof fn guarantee_condition_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action (without weak fairness).
        spec.entails(always(lift_action(cluster.next()))),
        // The vd type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        // The vd controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    ensures
        spec.entails(always(lift_state(vd_guarantee(controller_id))))
{
    let invariant = vd_guarantee(controller_id);

    cluster.lemma_always_cr_states_are_unmarshallable::<VDeploymentReconciler, VDeploymentReconcileState, VDeploymentView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    helper_invariants::lemma_always_vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(spec, cluster, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& helper_invariants::vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(helper_invariants::vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        VDeploymentView::marshal_preserves_integrity();
        VDeploymentReconcileState::marshal_preserves_integrity();
        PodView::marshal_preserves_integrity();

        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(req_msg_opt) => {
                let req_msg = req_msg_opt.unwrap();

                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content.is_APIRequest()
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content.get_APIRequest_0() {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vd_guarantee_create_req(req)(s_prime),
                    APIRequest::GetThenUpdateRequest(req) => vd_guarantee_get_then_update_req(req)(s_prime),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
            Step::ControllerStep((id, _, cr_key_opt)) => {
                let cr_key = cr_key_opt.get_Some_0();
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content.is_APIRequest()
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content.get_APIRequest_0() {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vd_guarantee_create_req(req)(s_prime),
                    APIRequest::GetThenUpdateRequest(req) => vd_guarantee_get_then_update_req(req)(s_prime),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

                    if id == controller_id {
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());
                        if new_msgs.contains(msg) && msg.content.is_get_then_update_request() {
                            assert(s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg.unwrap() == msg);
                            let req = msg.content.get_get_then_update_request();
                            let state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();    

                            assert(req.owner_ref == triggering_cr.controller_owner_ref());

                            if state.new_vrs.is_Some() && state.old_vrs_list.len() > 0 {
                                let old_vrs = state.old_vrs_list.last();
                                let updated_vrs = VReplicaSetView {
                                    spec: VReplicaSetSpecView {
                                        replicas: Some(0 as int),
                                        ..old_vrs.spec
                                    },
                                    ..old_vrs
                                };
                                assert(req.obj == updated_vrs.marshal()
                                    || req.obj == state.new_vrs.unwrap().marshal());
                            } else if state.old_vrs_list.len() > 0 {
                                let old_vrs = state.old_vrs_list.last();
                                let updated_vrs = VReplicaSetView {
                                    spec: VReplicaSetSpecView {
                                        replicas: Some(0 as int),
                                        ..old_vrs.spec
                                    },
                                    ..old_vrs
                                };
                                assert(req.obj == updated_vrs.marshal());
                            } else if state.new_vrs.is_Some() {
                                assert(req.obj == state.new_vrs.unwrap().marshal());
                            }
                            assert(req.obj.metadata.owner_references_contains(triggering_cr.controller_owner_ref()));
                            assert(exists |vd: VDeploymentView| 
                                req.owner_ref == #[trigger] vd.controller_owner_ref()
                                && req.obj.metadata.owner_references_contains(vd.controller_owner_ref())
                            );
                        }
                    }

                    
    //                  assert(match msg.content.get_APIRequest_0() {
    //                 APIRequest::ListRequest(_) => true,
    //                 APIRequest::CreateRequest(req) => vd_guarantee_create_req(req)(s_prime),
    //                 APIRequest::GetThenUpdateRequest(req) => {
    //     &&& req.obj.kind == VReplicaSetView::kind()
    //     &&& exists |vd: VDeploymentView|
    //         req.owner_ref == #[trigger] vd.controller_owner_ref()
    //         && req.obj.metadata.owner_references_contains(vd.controller_owner_ref())
    // },
    //                 _ => false, 
    //             });
                }
            }
            _ => {
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content.is_APIRequest()
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content.get_APIRequest_0() {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vd_guarantee_create_req(req)(s_prime),
                    APIRequest::GetThenUpdateRequest(req) => vd_guarantee_get_then_update_req(req)(s_prime),
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
