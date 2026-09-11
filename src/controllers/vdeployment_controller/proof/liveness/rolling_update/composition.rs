use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::reconciler::spec::io::*;
use verus_temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_lemmas::*, liveness::{spec::*, terminate, resource_match::*, proof::*, api_actions::*, rolling_update::resource_match::*}, predicate::*},
    proof::liveness::rolling_update::{predicate::*, helper_lemmas::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*}
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*; // shortcut for steps
use crate::vdeployment_controller::proof::helper_invariants;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
use vstd::{prelude::*, set_lib::*, map_lib::*, multiset::*};
use crate::vstd_ext::{set_lib::*, map_lib::*};

verus! {

// *** Rolling update ESR composition helpers ***
// TODO: fix after every_vrs_in_etcd_has_one_controller_owner is removed

pub open spec fn conjuncted_desired_state_is_vrs(vrs_set: Set<VReplicaSetView>) -> StatePred<ClusterState> {
    |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> vrs_liveness::desired_state_is(vrs)(s))
}

pub open spec fn conjuncted_current_state_matches_vrs(vrs_set: Set<VReplicaSetView>) -> StatePred<ClusterState> {
    |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> vrs_liveness::current_state_matches(vrs)(s))
}

// Compute the absolute difference between desired replicas and new VRS replicas
// This is the ranking function for iterative_esr
pub open spec fn replicas_diff(vd: VDeploymentView, new_vrs: VReplicaSetView) -> nat {
    let desired = get_replicas(vd.spec.replicas);
    let current = get_replicas(new_vrs.spec.replicas);
    if desired >= current {
        (desired - current) as nat
    } else {
        (current - desired) as nat
    }
}

pub open spec fn desired_state_is_vrs_with_key(vd: VDeploymentView, vrs: VReplicaSetView, vrs_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& vrs_liveness::desired_state_is(vrs)(s)
        &&& vrs.object_ref() == vrs_key
        &&& valid_owned_vrs(vrs, vd)
    }
}

pub open spec fn desired_state_is_vrs_with_replicas_diff_and_key(vd: VDeploymentView, vrs: VReplicaSetView, vrs_key: ObjectRef, diff: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // don't touch vrs if there is no need to patch replicas
        let vrs_with_replicas = vrs.with_spec(vrs.spec.with_replicas(
            if get_replicas(vd.spec.replicas) > get_replicas(vrs.spec.replicas) {
                get_replicas(vd.spec.replicas) - diff
            } else {
                get_replicas(vd.spec.replicas) + diff
            }
        ));
        &&& vrs_liveness::desired_state_is(vrs_with_replicas)(s)
        &&& vrs.object_ref() == vrs_key
        &&& valid_owned_vrs(vrs, vd)
    }
}

pub open spec fn current_state_matches_vrs_with_replicas_diff_and_key(vd: VDeploymentView, vrs: VReplicaSetView, vrs_key: ObjectRef, diff: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vrs_with_replicas = vrs.with_spec(vrs.spec.with_replicas(
            if get_replicas(vd.spec.replicas) > get_replicas(vrs.spec.replicas) {
                get_replicas(vd.spec.replicas) - diff
            } else {
                get_replicas(vd.spec.replicas) + diff
            }
        ));
        &&& vrs_liveness::current_state_matches(vrs_with_replicas)(s)
        &&& vrs.object_ref() == vrs_key
        &&& valid_owned_vrs(vrs, vd)
    }
}

pub open spec fn is_old_vrs_of(vrs: VReplicaSetView, vd: VDeploymentView, new_vrs_key: ObjectRef) -> bool {
    valid_owned_vrs(vrs, vd) && vrs.object_ref() != new_vrs_key
}

pub open spec fn old_vrs_set_is_owned_by_vd(vrs_set: Set<VReplicaSetView>, vd: VDeploymentView, new_vrs_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& vrs_set == s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key))
            .map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs))
        &&& forall |vrs| #[trigger] vrs_set.contains(vrs) ==> get_replicas(vrs.spec.replicas) == 0
    }
}

pub proof fn lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_with_nv_key(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs_key: ObjectRef, s: ClusterState, s_prime: ClusterState
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s),
    vd_rely_condition(cluster, controller_id)(s),
    cluster.next()(s, s_prime),
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
ensures
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s_prime)
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    let new_msgs = s_prime.in_flight().sub(s.in_flight());
    match step {
        Step::APIServerStep(input) => {
            lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_during_api_server_step(
                vd, controller_id, cluster, new_vrs_key, s, s_prime, input
            )
        },
        Step::ControllerStep(input) => {
            lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_during_controller_step(
                vd, controller_id, cluster, new_vrs_key, s, s_prime, input
            )
        },
        _ => { // this branch is slow
            // Maintain quantified invariant.
            if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                assert forall |msg| {
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.src is APIServer
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd, msg, s) by {
                    if !new_msgs.contains(msg) {
                        assert(s.in_flight().contains(msg));
                    }
                }
            }
        }
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_during_api_server_step(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs_key: ObjectRef, s: ClusterState, s_prime: ClusterState, input: Option<Message>
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s),
    vd_rely_condition(cluster, controller_id)(s),
    cluster.next_step(s, s_prime, Step::APIServerStep(input)),
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
ensures
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s_prime)
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    let msg = input->0;
    let (uid, key) = choose |nv_uid_key: (Uid, ObjectRef)| {
        &&& #[trigger] etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), 0)(s)
    };
    let new_msgs = s_prime.in_flight().sub(s.in_flight());
    let local_state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let local_state_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    assert(local_state == local_state_prime);
    assert(s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0
        == s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0);
    if s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()) {
        VDeploymentReconcileState::marshal_preserves_integrity();
        VReplicaSetView::marshal_preserves_integrity();
        if msg.src != HostId::Controller(controller_id, vd.object_ref()) {
            lemma_api_request_other_than_pending_req_msg_maintains_current_state_matches_with_nv_key(
                s, s_prime, vd, cluster, controller_id, msg, new_vrs_key
            );
            let obj = s.resources()[new_vrs_key];
            let etcd_vrs = VReplicaSetView::unmarshal(obj)->Ok_0;
            let etcd_vrs_prime = VReplicaSetView::unmarshal(s_prime.resources()[new_vrs_key])->Ok_0;
            assert(etcd_vrs.spec == etcd_vrs_prime.spec) by {
                assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
                    assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
                }
                // etcd_vrs's spec is not updated
                lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                    s, s_prime, vd, cluster, controller_id, msg
                );
            }
            if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                assert(s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg is Some);
                let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                assert(req_msg_is_list_vrs_req(vd, controller_id, req_msg, s));
                assert forall |resp_msg| {
                    &&& #[trigger] s_prime.in_flight().contains(resp_msg)
                    &&& resp_msg.src is APIServer
                    &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s_prime) by {
                    assert(s.in_flight().contains(resp_msg)) by {
                        if !s.in_flight().contains(resp_msg) {
                            assert(new_msgs.contains(resp_msg));
                            assert(!resp_msg_matches_req_msg(resp_msg, req_msg));
                        }
                    }
                    lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg, Some(uid)
                    );
                    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                    let vrs_list = objects_to_vrs_list(resp_objs)->0;
                    let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
                    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies {
                        let key = vrs.object_ref();
                        let etcd_vrs = VReplicaSetView::unmarshal(s_prime.resources()[key])->Ok_0;
                        &&& s_prime.resources().contains_key(key)
                        &&& VReplicaSetView::unmarshal(s_prime.resources()[key]) is Ok
                        &&& valid_owned_obj_key(vd, s_prime)(key)
                        &&& etcd_vrs.metadata.without_resource_version() == vrs.metadata.without_resource_version()
                        &&& etcd_vrs.spec == vrs.spec
                    } by {
                        let key = vrs.object_ref();
                        let etcd_obj = s.resources()[key];
                        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
                            assert(etcd_vrs.metadata.without_resource_version() == vrs.metadata.without_resource_version());
                            VReplicaSetView::marshal_preserves_integrity();
                        }
                        lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                            s, s_prime, vd, cluster, controller_id, msg
                        );
                    }
                }
            }
        } else {
            assert(s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()));
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            assert(input == Some(req_msg));
            if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
                let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                assert forall |msg| {
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.src is APIServer
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd, msg, s_prime) by {
                    if !new_msgs.contains(msg) {
                        assert(s.in_flight().contains(msg));
                    } else {
                        lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
                            s, s_prime, vd, cluster, controller_id, req_msg
                        );
                    }
                }
            }
        }
    } else {
        assert(msg.src != HostId::Controller(controller_id, vd.object_ref()));
        lemma_api_request_other_than_pending_req_msg_maintains_current_state_matches_with_nv_key(
            s, s_prime, vd, cluster, controller_id, msg, new_vrs_key
        );
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_during_controller_step(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs_key: ObjectRef, s: ClusterState, s_prime: ClusterState, input: (int, Option<Message>, Option<ObjectRef>)
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s),
    vd_rely_condition(cluster, controller_id)(s),
    cluster.next_step(s, s_prime, Step::ControllerStep(input)),
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
ensures
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s_prime)
{
    VDeploymentView::marshal_preserves_integrity();
    VDeploymentReconcileState::marshal_preserves_integrity();
    let step = choose |step| cluster.next_step(s, s_prime, step);
    assert(instantiated_etcd_state_is_with_zero_old_vrs_and_nv_key(vd, controller_id, new_vrs_key)(s)) by {
        lemma_esr_equiv_to_instantiated_etcd_state_is_with_nv_key(vd, cluster, controller_id, new_vrs_key, s);
    }
    let (uid, key) = choose |nv_uid_key: (Uid, ObjectRef)| {
        &&& #[trigger] etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), 0)(s)
    };
    let new_msgs = s_prime.in_flight().sub(s.in_flight());
    if s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
        && input.0 == controller_id && input.2 == Some(vd.object_ref()) {
        let resp_msg = input.1->0;
        if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
            // similar to proof in lemma_from_init_to_current_state_matches_with_nv_key, yet replicas and old_vrs_list_len are fixed
            let nv_uid_key_replicas_status = inductive_current_state_matches_implies_filter_old_and_new_vrs_from_resp_objs(
                vd, cluster, controller_id, resp_msg, new_vrs_key, s
            );
            lemma_from_list_resp_with_nv_to_next_state(
                s, s_prime, vd, cluster, controller_id, resp_msg, nv_uid_key_replicas_status, new_vrs_key
            );
            // let next_local_state = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
            // assert(next_local_state.old_vrs_index == 0);
            // let etcd_obj = s_prime.resources()[new_vrs_key];
            // let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
            // if next_local_state.new_vrs is Some && get_replicas(etcd_vrs.spec.replicas) > 0 {
            //     assert(next_local_state.new_vrs->0.object_ref() == new_vrs_key);
            //     assert(next_local_state.new_vrs->0.metadata.uid->0 == etcd_vrs.metadata.uid->0);
            // }
            // assert(next_local_state.new_vrs is Some && next_local_state.new_vrs->0.object_ref() != new_vrs_key ==> {
            //     &&& get_replicas(vd.spec.replicas) == 0 // optional, can be implied from above
            //     &&& next_local_state.new_vrs->get_replicas(0.spec.replicas) == 0
            // });
            // assert(at_vd_step_with_vd(vd, controller_id, at_step_or![Init, AfterListVRS, AfterScaleNewVRS, AfterEnsureNewVRS, Done, Error])(s_prime));
            // if at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS])(s_prime) {
            //     let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            //     assert(next_local_state.new_vrs is Some);
            //     assert(next_local_state.new_vrs->0.object_ref() == new_vrs_key);
            //     assert(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg is Some);
            //     assert(ru_req_msg_is_scale_new_vrs_by_one_req(vd, controller_id, req_msg)(s_prime));
            // } else {
            //     assert(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg is None);
            // }
            // assert(current_state_matches_with_new_vrs_key(vd, new_vrs_key)(s_prime));
            // assert(inductive_current_state_matches(vd, controller_id, new_vrs_key)(s_prime));
        } else if at_vd_step_with_vd(vd, controller_id, at_step![Init])(s) {
            // prove that the newly sent message has no response.
            if s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg is Some {
                let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg));
                assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
                    && (forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id)
                    && s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)
                    && msg != req_msg
                    implies msg.rpc_id != req_msg.rpc_id by {
                    if !s.in_flight().contains(msg) {} // need this to invoke trigger.
                }
            }
        } else if at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS])(s) {
            // it directly goes to Done
        } else if at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS])(s) {
        }
    } else if !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()) {
        if s_prime.ongoing_reconciles(controller_id).contains_key(vd.object_ref()) { // RunScheduledReconcile
            assert(s_prime.resources() == s.resources());
            assert(at_vd_step_with_vd(vd, controller_id, at_step![Init])(s_prime)) by {
                assert(helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)(s_prime));
                lemma_cr_fields_eq_to_cr_predicates_eq(vd, controller_id, s_prime);
            }
        } else {
            assert(s_prime.resources() == s.resources());
        }
    } else { // same controller_id, different CR
        // assert(s.ongoing_reconciles(controller_id)[vd.object_ref()] == s_prime.ongoing_reconciles(controller_id)[vd.object_ref()]);
        assert(s.resources() == s_prime.resources());
        if at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s) {
            let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            assert forall |msg| {
                &&& #[trigger] s_prime.in_flight().contains(msg)
                &&& msg.src is APIServer
                &&& resp_msg_matches_req_msg(msg, req_msg)
            } implies resp_msg_is_ok_list_resp_containing_matched_vrs(vd, msg, s) by {
                if !new_msgs.contains(msg) {
                    assert(s.in_flight().contains(msg));
                }
            }
        }
    }
}

// *** Obligation proofs for iterative_esr (per fixed vrs_set) ***

// Obligation 1: ESR for each ranking level
// spec |= [] desired_vrs ~> [] matches_vrs
pub proof fn esr_for_each_ranking(
    spec: TempPred<ClusterState>, vrs_set: Set<VReplicaSetView>, vd: VDeploymentView, new_vrs_key: ObjectRef
)
    requires
        spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
    ensures
        spec.entails(
            always(lift_state(conjuncted_desired_state_is_vrs(vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key))))
        .leads_to(
            always(lift_state(conjuncted_current_state_matches_vrs(vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)))))),
{
    // Instantiate VRS ESR for each vrs in the set
    assert forall |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) implies
        spec.entails(always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))) by {
        tla_forall_p_tla_forall_q_equality(
            |vrs| vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs),
            |vrs| always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))
        );
        spec_entails_tla_forall_apply(spec, |vrs| always(lift_state(vrs_liveness::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))), vrs);
    }
    // Compose individual VRS ESRs into the conjuncted form
    let desired_state_is_vrs = |vrs| vrs_liveness::desired_state_is(vrs);
    let current_state_matches_vrs = |vrs| vrs_liveness::current_state_matches(vrs);
    assert(conjuncted_desired_state_is_vrs(vrs_set)
        == |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs(vrs)(s)));
    assert(conjuncted_current_state_matches_vrs(vrs_set)
        == |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> current_state_matches_vrs(vrs)(s)));
    spec_entails_always_tla_forall_leads_to_always_tla_forall_within_domain(
        spec, desired_state_is_vrs, current_state_matches_vrs, vrs_set,
        conjuncted_desired_state_is_vrs(vrs_set), conjuncted_current_state_matches_vrs(vrs_set)
    );
    // Combine with self-leads-to for owned
    leads_to_self(always(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key))));
    always_leads_to_always_and(spec,
        lift_state(conjuncted_desired_state_is_vrs(vrs_set)),
        lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)),
        lift_state(conjuncted_current_state_matches_vrs(vrs_set)),
        lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key))
    );
}

// Obligation 2: Monotonicity (ranking never increases)
// forall n. spec |= [] (p(n) => [] (exists m <= n. p(m)))
// flaky
#[verifier(spinoff_prover)]
pub proof fn ranking_never_increases(
    spec: TempPred<ClusterState>, new_vrs: VReplicaSetView, new_vrs_key: ObjectRef, vd: VDeploymentView, controller_id: int, cluster: Cluster
)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    ensures
        forall |n| spec.entails(always(lift_state(#[trigger] desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n))
            .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
        .implies(always(tla_exists(|m: nat| lift_state(|s| m <= n).and(
            lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
        ))))),
{
    // use next_monotonic_to_always_exists
    let p = |n: nat| and!(
        desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n),
        inductive_current_state_matches(vd, controller_id, new_vrs_key)
    );
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s_prime)
        &&& vd_rely_condition(cluster, controller_id)(s)
        &&& vd_rely_condition(cluster, controller_id)(s_prime)
    };
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
    always_to_always_later(spec, lifted_vd_reconcile_request_only_interferes_with_itself(controller_id));
    always_to_always_later(spec, lifted_vd_rely_condition(cluster, controller_id));
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id),
        later(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)),
        lifted_vd_rely_condition(cluster, controller_id),
        later(lifted_vd_rely_condition(cluster, controller_id))
    );
    assert forall |n: nat| lift_state(p(n)) == lift_state(#[trigger] desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))) by {
        and_eq(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n), inductive_current_state_matches(vd, controller_id, new_vrs_key));
    }
    // pre, inv is preserved
    assert forall |n| #![trigger p(n)] forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) && p(n)(s) ==> exists |m: nat| m <= n && #[trigger] p(m)(s_prime) by {
        // #![trigger p(m)] reduce the flakiness here in a strange way
        assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) && p(n)(s) implies exists |m: nat| #![trigger p(m)] m <= n && #[trigger] p(m)(s_prime) by {
            lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_with_nv_key(vd, controller_id, cluster, new_vrs_key, s, s_prime);
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    let msg = input->0;
                    if msg.src == HostId::Controller(controller_id, vd.object_ref()) {
                        if ru_req_msg_is_scale_new_vrs_by_one_req(vd, controller_id, msg)(s) {
                            ranking_never_increases_from_s_to_s_prime(vd, controller_id, cluster, s, s_prime, new_vrs, new_vrs_key, n, msg);
                        } else {
                            assert(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n)(s_prime));
                            assert(p(n)(s_prime));
                        }
                    } else {
                        let obj = s.resources()[new_vrs_key];
                        assert(s.resources().contains_key(new_vrs_key)); // trigger
                        assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
                            // each_object_in_etcd_has_at_most_one_controller_owner
                            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
                        }
                        lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(s, s_prime, vd, cluster, controller_id, msg);
                    }
                },
                _ => {
                    assert(s_prime.resources() == s.resources());
                    assert(p(n)(s_prime));
                }
            }
        }
    }
    assert forall |n: nat| spec.entails(always(lift_state(#[trigger] p(n)).implies(always(tla_exists(|m: nat| lift_state(|s| m <= n).and(lift_state(p(m)))))))) by {
        next_monotonic_to_always_exists(spec, stronger_next, p);
    }
    assert forall |n| spec.entails(always(lift_state(#[trigger] desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
    .implies(always(tla_exists(|m: nat| lift_state(|s| m <= n)
        .and(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
    ))))) by {
        tla_exists_p_tla_exists_q_equality(
            |m: nat| lift_state(|s| m <= n).and(lift_state(p(m))),
            |m: nat| lift_state(|s| m <= n)
                .and(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m))
                .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
        );
    }
}

proof fn ranking_never_increases_from_s_to_s_prime(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, s: ClusterState, s_prime: ClusterState, new_vrs: VReplicaSetView, new_vrs_key: ObjectRef, n: nat, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s_prime),
    vd_rely_condition(cluster, controller_id)(s),
    vd_rely_condition(cluster, controller_id)(s_prime),
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s_prime),
    desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n)(s),
    req_msg.src == HostId::Controller(controller_id, vd.object_ref()),
    ru_req_msg_is_scale_new_vrs_by_one_req(vd, controller_id, req_msg)(s)
ensures
    exists |m: nat| m <= n && #[trigger] desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m)(s_prime)
{
    let req = req_msg.content->APIRequest_0->GetThenUpdateRequest_0;
    let req_vrs = VReplicaSetView::unmarshal(req.obj)->Ok_0;
    let req_vrs_replicas = get_replicas(req_vrs.spec.replicas);
    assert(req.key() == new_vrs_key);
    let new_vrs_prime = VReplicaSetView::unmarshal(s_prime.resources()[new_vrs_key])->Ok_0;
    assert(get_replicas(new_vrs_prime.spec.replicas) == req_vrs_replicas);
    let m = replicas_diff(vd, new_vrs_prime);
    assert(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m)(s_prime));
    assert(m <= n);
}

// Obligation 3: Ranking decrease
// forall n > 0. spec |= [] q(n) ~> !p(n)
// Prove with a specialized version of ESR proof with spec |= [] current_state_matches
pub proof fn ranking_decreases_after_vrs_esr(
    spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs: VReplicaSetView, new_vrs_key: ObjectRef, diff: nat
)
    requires
        diff > 0,
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(next_with_wf(cluster, controller_id)),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        // spec_entails_always_desired_state_is_leads_to_assumption_and_invariants_of_all_phases
        spec.entails(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)),
    ensures
        spec.entails(always(
            lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))
            .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
            .and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))))
        .leads_to(not(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))
            .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))))),
{
    let post = not(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))));
    if new_vrs.object_ref() != new_vrs_key { // trivial
        temp_pred_equality(
            lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)),
            false_pred()
        );
        temp_pred_equality(
            lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))
                .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
                .and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))),
            false_pred()
        );
        false_is_stable::<ClusterState>();
        stable_to_always(false_pred::<ClusterState>());
        false_leads_to_anything::<ClusterState>(spec, post);
        return;
    }
    let stable_spec = next_with_wf(cluster, controller_id)
        .and(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)))
        .and(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))))
        .and(always(lifted_vd_rely_condition(cluster, controller_id)))
        .and(assumption_and_invariants_of_all_phases(vd, cluster, controller_id));
    next_with_wf_is_stable(cluster, controller_id);
    always_p_is_stable(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id));
    always_p_is_stable(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
    always_p_is_stable(lifted_vd_rely_condition(cluster, controller_id));
    assumption_and_invariants_of_all_phases_is_stable(vd, cluster, controller_id);
    stable_and_n!(
        next_with_wf(cluster, controller_id),
        always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)),
        always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))),
        always(lifted_vd_rely_condition(cluster, controller_id)),
        assumption_and_invariants_of_all_phases(vd, cluster, controller_id)
    );
    combine_spec_entails_n!(spec,
        stable_spec,
        next_with_wf(cluster, controller_id),
        always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)),
        always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))),
        always(lifted_vd_rely_condition(cluster, controller_id)),
        assumption_and_invariants_of_all_phases(vd, cluster, controller_id)
    );
    let composed_spec = stable_spec.and(
        always(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)))
        .and(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref()))))
        .and(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)))));
    // 0. unpack invariants from cluster_invariants_since_reconciliation
    entails_trans(composed_spec, stable_spec, always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))));
    entails_always_unpack_n!(composed_spec,
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        lift_state(helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(desired_state_is(vd))
    );
    entails_trans(composed_spec, stable_spec, next_with_wf(cluster, controller_id));
    always_to_always_later(composed_spec, lift_state(desired_state_is(vd)));
    // 1. termination, true ~> reconcile_idle
    // same as lemma_true_leads_to_always_current_state_matches
    let reconcile_idle = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
    };
    assert(composed_spec.entails(true_pred().leads_to(lift_state(reconcile_idle)))) by {
        terminate::reconcile_eventually_terminates(composed_spec, cluster, controller_id);
        spec_entails_tla_forall_apply(composed_spec, |key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))), vd.object_ref());
    }
    // reconcile_idle ~> reconcile_scheduled
    let reconcile_scheduled = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(vd.object_ref())
    };
    assert(composed_spec.entails(lift_state(reconcile_idle).leads_to(lift_state(reconcile_scheduled)))) by {
        let input = vd.object_ref();
        let stronger_reconcile_idle = |s: ClusterState| {
            &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
            &&& !s.scheduled_reconciles(controller_id).contains_key(vd.object_ref())
        };
        let stronger_next = |s, s_prime| {
            &&& cluster.next()(s, s_prime)
            &&& desired_state_is(vd)(s)
            &&& desired_state_is(vd)(s_prime)
        };
        combine_spec_entails_always_n!(
            composed_spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(desired_state_is(vd)),
            later(lift_state(desired_state_is(vd)))
        );
        cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(
            composed_spec, controller_id, input, stronger_next, and!(stronger_reconcile_idle, desired_state_is(vd)), reconcile_scheduled
        );
        temp_pred_equality(
            lift_state(stronger_reconcile_idle).and(lift_state(desired_state_is(vd))),
            lift_state(and!(stronger_reconcile_idle, desired_state_is(vd)))
        );
        leads_to_by_borrowing_inv(composed_spec, lift_state(stronger_reconcile_idle), lift_state(reconcile_scheduled), lift_state(desired_state_is(vd)));
        entails_implies_leads_to(composed_spec, lift_state(reconcile_scheduled), lift_state(reconcile_scheduled));
        or_leads_to(composed_spec, lift_state(stronger_reconcile_idle), lift_state(reconcile_scheduled), lift_state(reconcile_scheduled));
        temp_pred_equality(lift_state(stronger_reconcile_idle).or(lift_state(reconcile_scheduled)), lift_state(reconcile_idle));
    }
    let init = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Init]),
        no_pending_req_in_cluster(vd, controller_id)
    );
    // 2. reconcile_idle ~> init
    assert(composed_spec.entails(lift_state(reconcile_scheduled).leads_to(lift_state(init)))) by {
        let input = (None, Some(vd.object_ref()));
        let stronger_next = |s, s_prime| {
            &&& cluster.next()(s, s_prime) 
            &&& Cluster::crash_disabled(controller_id)(s) 
            &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s) 
            &&& helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)(s_prime) 
            &&& Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)(s_prime)
        };
        always_to_always_later(composed_spec, lift_state(helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)));
        always_to_always_later(composed_spec, lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)));
        combine_spec_entails_always_n!(
            composed_spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(Cluster::crash_disabled(controller_id)),
            lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
            later(lift_state(helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id))),
            later(lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)))
        );
        assert forall |s, s_prime| reconcile_scheduled(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies init(s_prime) by {
            VDeploymentReconcileState::marshal_preserves_integrity();
            lemma_cr_fields_eq_to_cr_predicates_eq(vd, controller_id, s_prime);
        }
        cluster.lemma_pre_leads_to_post_by_controller(
            composed_spec, controller_id, input, stronger_next, ControllerStep::RunScheduledReconcile, reconcile_scheduled, init
        );
    }
    // 3. init ~> after_list ~> after_scale_new_vrs ~> !desired_state_is
    assert(composed_spec.entails(lift_state(init).leads_to(post))) by {
        lemma_from_init_to_not_desired_state_is(vd, composed_spec, cluster, controller_id, new_vrs, diff);
    }
    leads_to_trans_n!(
        composed_spec, true_pred(), lift_state(reconcile_idle), lift_state(reconcile_scheduled), lift_state(init), post
    );
    assert(stable_spec.entails(always(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
        .and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))))
        .leads_to(post))) by {
        let c = always(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)))
            .and(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref()))))
            .and(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff))));
        temp_pred_equality(true_pred().and(c), c);
        always_and_equality_n!(
            lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)),
            lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)),
            lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))
        );
        temp_pred_equality(
            composed_spec,
            stable_spec.and(c)
        );
        unpack_conditions_from_spec(stable_spec, c, true_pred(), post);
    }
    // spec |= always(stable_spec) == stable_spec (since stable_spec is stable)
    entails_trans(
        spec,
        stable_spec,
        always(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff))
            .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
            .and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)))
        ).leads_to(post)
    );
}

// From inductive_current_state_matches, extract (vrs_set, n) witness
pub proof fn current_state_match_vd_implies_exists_old_vrs_set(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, new_vrs_key: ObjectRef, s: ClusterState
) -> (vrs_set: Set<VReplicaSetView>) // vrs_set, new_vrs, replicas_diff
    requires
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
        current_state_matches_with_new_vrs_key(vd, new_vrs_key)(s),
    ensures
        old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)(s),
        conjuncted_desired_state_is_vrs(vrs_set)(s),
{
    let vrs_set = s.resources().values()
        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
        .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key))
        .map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs));
    // |= conjuncted_desired_state_is_vrs(vrs_set)(s)
    assert forall |vrs| #[trigger] vrs_set.contains(vrs) implies vrs_liveness::desired_state_is(vrs)(s) && get_replicas(vrs.spec.replicas) == 0 by {
        VReplicaSetView::marshal_preserves_integrity();
        let etcd_obj = choose |obj: DynamicObjectView| #[trigger] s.resources().values().contains(obj) && obj.object_ref() == vrs.object_ref();
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        assert(exists |vrs_with_rv_status| vrs_with_no_rv_status(vrs_with_rv_status) == vrs
            && s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key)).contains(vrs_with_rv_status));
        let vrs_with_rv_status = choose |vrs_with_rv_status| vrs_with_no_rv_status(vrs_with_rv_status) == vrs
            && s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key)).contains(vrs_with_rv_status);
        assert(s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0).contains(vrs_with_rv_status));
        assert(exists |etcd_obj| #![trigger s.resources().values().contains(etcd_obj)]
            VReplicaSetView::unmarshal(etcd_obj)->Ok_0 == vrs_with_rv_status
            && s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(etcd_obj));
        let etcd_obj2 = choose |etcd_obj| #![trigger s.resources().values().contains(etcd_obj)]
            VReplicaSetView::unmarshal(etcd_obj)->Ok_0 == vrs_with_rv_status
            && s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(etcd_obj);
        assert(etcd_obj2.object_ref() == vrs.object_ref());
        assert(etcd_obj2 == etcd_obj);
        assert(valid_owned_vrs(vrs_with_rv_status, vd));
        assert(etcd_obj.metadata.owner_references is Some);
        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).len() == 1) by {
            assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).len() <= 1);
            assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
        }
        assert(vrs_liveness::desired_state_is(etcd_vrs)(s));
        if get_replicas(vrs.spec.replicas) > 0 {
            let etcd_new_vrs = VReplicaSetView::unmarshal(s.resources()[new_vrs_key])->Ok_0;
            assert(get_replicas(vrs_with_rv_status.spec.replicas) > 0);
            assert(valid_owned_obj_key(vd, s)(vrs.object_ref()));
            assert(filter_old_vrs_keys(Some(etcd_new_vrs.metadata.uid->0), s)(vrs.object_ref()));
            assert(false);
        }
    }
    assert({
        vrs_set == s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key))
            .map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs))
    });
    return vrs_set;
}

// q(0) with vrs_set identity implies composed_current_state_matches
pub proof fn conjuncted_current_state_matches_old_vrs_0_implies_composed(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, vrs_set: Set<VReplicaSetView>, new_vrs: VReplicaSetView, new_vrs_key: ObjectRef, s: ClusterState
)
    requires
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
        conjuncted_current_state_matches_vrs(vrs_set)(s),
        inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
        desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)(s),
        current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)(s),
        old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)(s),
    ensures
        composed_current_state_matches(vd)(s),
{
    VReplicaSetView::marshal_preserves_integrity();
    // new_vrs replicas might be updated during reconciliation
    let new_vrs = new_vrs.with_spec(new_vrs.spec.with_replicas(get_replicas(vd.spec.replicas)));
    assert(s.resources().values().filter(valid_owned_pods(vd, s)) == vrs_liveness::matching_pods(new_vrs, s.resources())) by {
        assert forall |obj: DynamicObjectView| #[trigger] s.resources().values().contains(obj)
            implies valid_owned_pods(vd, s)(obj) == vrs_liveness::owned_selector_match_is(new_vrs, obj) by {
            if valid_owned_pods(vd, s)(obj) && !vrs_liveness::owned_selector_match_is(new_vrs, obj) {
                let havoc_vrs = choose |vrs: VReplicaSetView| {
                    &&& #[trigger] vrs_liveness::owned_selector_match_is(vrs, obj)
                    &&& valid_owned_vrs(vrs, vd)
                    &&& s.resources().contains_key(vrs.object_ref())
                    &&& VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0 == vrs
                };
                if havoc_vrs.object_ref() == new_vrs_key {
                    assert(havoc_vrs.controller_owner_ref() == new_vrs.controller_owner_ref());
                    assert(havoc_vrs.spec.selector == new_vrs.spec.selector);
                    assert(vrs_liveness::owned_selector_match_is(new_vrs, obj));
                } else {
                    assert(vrs_set.contains(vrs_with_no_rv_status(havoc_vrs))) by {
                        let etcd_obj = s.resources()[havoc_vrs.object_ref()];
                        assert(s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(etcd_obj));
                        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                        assert(s.resources().values()
                            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
                            .filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key))
                            .contains(etcd_vrs));
                        assert(vrs_with_no_rv_status(havoc_vrs) == vrs_with_no_rv_status(etcd_vrs));
                    }
                    assert(exists |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) 
                        && vrs_with_no_rv_status(vrs) == vrs_with_no_rv_status(havoc_vrs) && vrs != new_vrs);
                    let havoc_vrs_in_set = choose |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs)
                        && vrs_with_no_rv_status(vrs) == vrs_with_no_rv_status(havoc_vrs) && vrs != new_vrs;
                    assert(get_replicas(havoc_vrs_in_set.spec.replicas) > 0) by {
                        assert(vrs_liveness::matching_pods(havoc_vrs_in_set, s.resources()).len() > 0) by {
                            assert(vrs_liveness::matching_pods(havoc_vrs_in_set, s.resources()).contains(obj));
                            s.resources().lemma_injective_values_len();
                            lemma_set_empty_equivalency_len(vrs_liveness::matching_pods(havoc_vrs_in_set, s.resources()));
                        }
                    }
                    assert(false);
                }
            }
            if vrs_liveness::owned_selector_match_is(new_vrs, obj) && !valid_owned_pods(vd, s)(obj) {
                let new_vrs_in_etcd = VReplicaSetView::unmarshal(s.resources()[new_vrs_key])->Ok_0;
                assert({
                    &&& #[trigger] vrs_liveness::owned_selector_match_is(new_vrs_in_etcd, obj)
                    &&& valid_owned_vrs(new_vrs_in_etcd, vd)
                    &&& s.resources().contains_key(new_vrs_in_etcd.object_ref())
                    &&& VReplicaSetView::unmarshal(s.resources()[new_vrs_in_etcd.object_ref()])->Ok_0 == new_vrs_in_etcd
                });
                assert(false);
            }
        }
    }
}

// Stability of vrs_set identity (modulo rv/status/replicas) and conjuncted p(n)
pub proof fn composed_old_vrs_set_pre_preserves_from_s_to_s_prime(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, vrs_set: Set<VReplicaSetView>, new_vrs_key: ObjectRef, s: ClusterState, s_prime: ClusterState
)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
        Cluster::etcd_objects_have_unique_uids()(s),
        vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s),
        vd_rely_condition(cluster, controller_id)(s),
        cluster.next()(s, s_prime),
        inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
        inductive_current_state_matches(vd, controller_id, new_vrs_key)(s_prime),
        old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)(s),
        conjuncted_desired_state_is_vrs(vrs_set)(s),
    ensures
        old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)(s_prime),
        conjuncted_desired_state_is_vrs(vrs_set)(s_prime),
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    let vrs_set_prime = current_state_match_vd_implies_exists_old_vrs_set(vd, cluster, controller_id, new_vrs_key, s_prime);
    assert(vrs_set == vrs_set_prime) by {
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg.src != HostId::Controller(controller_id, vd.object_ref()) {
                    lemma_api_request_other_than_pending_req_msg_maintains_vrs_set_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                    let base_s = s.resources().values()
                        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
                        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
                        .map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs));
                    let base_s_prime = s_prime.resources().values()
                        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
                        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
                        .map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs));
                    assert(base_s == base_s_prime);
                    let unmarshal_s = s.resources().values()
                        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0);
                    let unmarshal_s_prime = s_prime.resources().values()
                        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0);

                    let key_filter = |vrs: VReplicaSetView| vrs.object_ref() != new_vrs_key;

                    set_filter_conj_is_filter_filter(
                        unmarshal_s,
                        |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd),
                        key_filter,
                        |vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key)
                    );
                    set_filter_conj_is_filter_filter(
                        unmarshal_s_prime,
                        |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd),
                        key_filter,
                        |vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key)
                    );
                    let owned_s = unmarshal_s.filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd));
                    let owned_s_prime = unmarshal_s_prime.filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd));
                    commutativity_of_set_map_and_filter(
                        owned_s,
                        key_filter,
                        key_filter,
                        |vrs: VReplicaSetView| vrs_with_no_rv_status(vrs)
                    );
                    commutativity_of_set_map_and_filter(
                        owned_s_prime,
                        key_filter,
                        key_filter,
                        |vrs: VReplicaSetView| vrs_with_no_rv_status(vrs)
                    );
                } else {
                    assert(msg == s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0);
                    if ru_req_msg_is_scale_new_vrs_by_one_req(vd, controller_id, msg)(s) {
                        let req = msg.content->APIRequest_0->GetThenUpdateRequest_0;
                        assert(req.key() == new_vrs_key);
                        // Only new_vrs_key is modified; old VRS objects have key != new_vrs_key
                        VReplicaSetView::marshal_preserves_integrity();
                        let unmarshal_s = s.resources().values()
                            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0);
                        let unmarshal_s_prime = s_prime.resources().values()
                            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
                            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0);
                        let old_filtered_s = unmarshal_s.filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key));
                        let old_filtered_s_prime = unmarshal_s_prime.filter(|vrs: VReplicaSetView| is_old_vrs_of(vrs, vd, new_vrs_key));
                        // Step 1: show old_filtered_s == old_filtered_s_prime
                        assert forall |vrs: VReplicaSetView| #[trigger] old_filtered_s.contains(vrs)
                            implies old_filtered_s_prime.contains(vrs) by {
                            assert(unmarshal_s.contains(vrs) && is_old_vrs_of(vrs, vd, new_vrs_key));
                            let etcd_obj = choose |obj: DynamicObjectView| #![trigger s.resources().values().contains(obj)] {
                                &&& s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(obj)
                                &&& VReplicaSetView::unmarshal(obj)->Ok_0 == vrs
                            };
                            let k = vrs.object_ref();
                            assert(k != new_vrs_key);
                            assert(s_prime.resources().contains_key(k));
                            assert(s_prime.resources()[k] == s.resources()[k]);
                            assert(s_prime.resources().values().contains(etcd_obj));
                            assert(s_prime.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(etcd_obj));
                            assert(unmarshal_s_prime.contains(vrs));
                        }
                        assert forall |vrs: VReplicaSetView| #[trigger] old_filtered_s_prime.contains(vrs)
                            implies old_filtered_s.contains(vrs) by {
                            assert(unmarshal_s_prime.contains(vrs) && is_old_vrs_of(vrs, vd, new_vrs_key));
                            let etcd_obj = choose |obj: DynamicObjectView| #![trigger s_prime.resources().values().contains(obj)] {
                                &&& s_prime.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(obj)
                                &&& VReplicaSetView::unmarshal(obj)->Ok_0 == vrs
                            };
                            let k = vrs.object_ref();
                            assert(k != new_vrs_key);
                            assert(s.resources().contains_key(k));
                            assert(s.resources()[k] == s_prime.resources()[k]);
                            assert(s.resources().values().contains(etcd_obj));
                            assert(s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(etcd_obj));
                            assert(unmarshal_s.contains(vrs));
                        }
                        // Step 2: old_filtered_s == old_filtered_s_prime implies mapped sets are equal
                        assert(old_filtered_s.map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs))
                            == old_filtered_s_prime.map(|vrs: VReplicaSetView| vrs_with_no_rv_status(vrs)));
                    }
                }
            },
            _ => {}
        }
    }
}

// *** Top-level rolling update ESR composition theorem ***

// The state-dependent parameters of the iterative ESR argument, packed into one predicate:
// the new vrs (as stored in etcd), the ranking (distance between desired and current replicas),
// and the set of old vrs owned by vd.
pub open spec fn rolling_update_witness_pred(
    vd: VDeploymentView, controller_id: int, new_vrs_key: ObjectRef, new_vrs: VReplicaSetView, n: nat, vrs_set: Set<VReplicaSetView>
) -> TempPred<ClusterState> {
    lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n))
    .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
    .and(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)))
    .and(lift_state(conjuncted_desired_state_is_vrs(vrs_set)))
}

// From inductive_current_state_matches at a state, extract the (new_vrs, ranking, old vrs set) witness.
pub proof fn rolling_update_witness(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, new_vrs_key: ObjectRef, s: ClusterState
) -> (t: (VReplicaSetView, nat, Set<VReplicaSetView>))
    requires
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
        inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
    ensures
        desired_state_is_vrs_with_replicas_diff_and_key(vd, t.0, new_vrs_key, t.1)(s),
        old_vrs_set_is_owned_by_vd(t.2, vd, new_vrs_key)(s),
        conjuncted_desired_state_is_vrs(t.2)(s),
{
    VReplicaSetView::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_metadata();
    let etcd_obj = s.resources()[new_vrs_key];
    let new_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
    let n = replicas_diff(vd, new_vrs);
    let vrs_set = current_state_match_vd_implies_exists_old_vrs_set(vd, cluster, controller_id, new_vrs_key, s);
    assert(s.resources().contains_key(new_vrs_key));
    assert(valid_owned_obj_key(vd, s)(new_vrs_key));
    assert(valid_owned_vrs(new_vrs, vd));
    assert(etcd_obj.metadata == new_vrs.metadata);
    assert(etcd_obj.metadata.owner_references is Some);
    assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).len() == 1) by {
        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).len() <= 1);
        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
    }
    let vrs_with_replicas = new_vrs.with_spec(new_vrs.spec.with_replicas(
        if get_replicas(vd.spec.replicas) > get_replicas(new_vrs.spec.replicas) {
            get_replicas(vd.spec.replicas) - n
        } else {
            get_replicas(vd.spec.replicas) + n
        }
    ));
    assert(vrs_with_replicas.spec.replicas == Some(get_replicas(new_vrs.spec.replicas)));
    assert(vrs_with_replicas.spec.with_replicas(vrs_with_replicas.spec.replicas.unwrap_or(1))
        == new_vrs.spec.with_replicas(new_vrs.spec.replicas.unwrap_or(1)));
    assert(vrs_liveness::desired_state_is(vrs_with_replicas)(s));
    assert(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, n)(s));
    (new_vrs, n, vrs_set)
}

// For a fixed witness (new_vrs, n, vrs_set), iterate the vrs ESR down the ranking until
// the new vrs matches vd.spec.replicas, and combine with ESR for the (zero-replica) old vrs set.
#[verifier(spinoff_prover)]
pub proof fn rolling_update_witness_leads_to_composed_current_state_matches(
    spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster,
    new_vrs_key: ObjectRef, new_vrs: VReplicaSetView, n: nat, vrs_set: Set<VReplicaSetView>
)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
        spec.entails(next_with_wf(cluster, controller_id)),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        spec.entails(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)),
    ensures
        spec.entails(rolling_update_witness_pred(vd, controller_id, new_vrs_key, new_vrs, n, vrs_set)
            .leads_to(always(lift_state(composed_current_state_matches(vd))))),
{
    let icsm = inductive_current_state_matches(vd, controller_id, new_vrs_key);
    let inv = cluster_invariants_since_reconciliation(cluster, vd, controller_id);
    let pre = rolling_update_witness_pred(vd, controller_id, new_vrs_key, new_vrs, n, vrs_set);
    let post = always(lift_state(composed_current_state_matches(vd)));
    if !(new_vrs.object_ref() == new_vrs_key && valid_owned_vrs(new_vrs, vd)) {
        // pre is unsatisfiable
        temp_pred_equality(pre, false_pred());
        false_leads_to_anything(spec, post);
        return;
    }
    let p = |m: nat| lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m))
        .and(lift_state(icsm));
    let q = |m: nat| lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m))
        .and(lift_state(icsm))
        .and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m)));
    // Obligation 1: forall m, spec |= []p(m) ~> []q(m), from ESR of the new vrs with m-adjusted replicas
    assert forall |m: nat| #![trigger p(m)] spec.entails(always(p(m)).leads_to(always(q(m)))) by {
        let vrs_m = new_vrs.with_spec(new_vrs.spec.with_replicas(
            if get_replicas(vd.spec.replicas) > get_replicas(new_vrs.spec.replicas) {
                get_replicas(vd.spec.replicas) - m
            } else {
                get_replicas(vd.spec.replicas) + m
            }
        ));
        let dsd = lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m));
        let csd = lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m));
        spec_entails_tla_forall_apply(spec, |vrs| vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs), vrs_m);
        temp_pred_equality(dsd, lift_state(vrs_liveness::desired_state_is(vrs_m)));
        temp_pred_equality(csd, lift_state(vrs_liveness::current_state_matches(vrs_m)));
        leads_to_self(always(p(m)));
        always_leads_to_always_and(spec, p(m), dsd, p(m), csd);
        temp_pred_equality(p(m).and(dsd), p(m));
        assert(q(m) == p(m).and(csd));
    }
    // Obligation 2: the ranking never increases
    ranking_never_increases(spec, new_vrs, new_vrs_key, vd, controller_id, cluster);
    assert forall |m: nat| #![trigger p(m)] spec.entails(always(p(m).implies(always(tla_exists(|j: nat| lift_state(|s| j <= m).and(p(j))))))) by {
        assert(spec.entails(always(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, m))
            .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
        .implies(always(tla_exists(|j: nat| lift_state(|s| j <= m).and(
            lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, j)).and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
        ))))));
        tla_exists_p_tla_exists_q_equality(
            |j: nat| lift_state(|s| j <= m).and(p(j)),
            |j: nat| lift_state(|s| j <= m)
                .and(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, j))
                .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))))
        );
    }
    // Obligation 3: the ranking eventually decreases
    assert forall |m: nat| #![trigger p(m)] m > 0 implies spec.entails(always(q(m)).leads_to(not(p(m)))) by {
        ranking_decreases_after_vrs_esr(spec, vd, controller_id, cluster, new_vrs, new_vrs_key, m);
    }
    iterative_esr(spec, p, q);
    // pre ~> p(n) ~> []p(0)
    assert(spec.entails(p(n).leads_to(always(p(0)))));
    entails_implies_leads_to(spec, pre, p(n));
    leads_to_trans(spec, pre, p(n), always(p(0)));
    // The old vrs set (and icsm) is preserved by every transition
    let rr = and!(
        old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key),
        conjuncted_desired_state_is_vrs(vrs_set),
        icsm
    );
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& inv(s)
        &&& inv(s_prime)
        &&& vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
    };
    temp_pred_equality(
        lift_state(vd_rely_condition(cluster, controller_id)),
        lifted_vd_rely_condition(cluster, controller_id)
    );
    temp_pred_equality(
        lift_state(vd_reconcile_request_only_interferes_with_itself_condition(controller_id)),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)
    );
    always_to_always_later(spec, lift_state(inv));
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(inv),
        later(lift_state(inv)),
        lift_state(vd_reconcile_request_only_interferes_with_itself_condition(controller_id)),
        lift_state(vd_rely_condition(cluster, controller_id))
    );
    assert forall |s, s_prime| rr(s) && #[trigger] stronger_next(s, s_prime) implies rr(s_prime) by {
        lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_with_nv_key(vd, controller_id, cluster, new_vrs_key, s, s_prime);
        composed_old_vrs_set_pre_preserves_from_s_to_s_prime(vd, controller_id, cluster, vrs_set, new_vrs_key, s, s_prime);
    }
    entails_implies_leads_to(spec, pre, lift_state(rr));
    leads_to_stable(spec, lift_action(stronger_next), pre, lift_state(rr));
    // pre ~> [](p(0) /\ rr)
    leads_to_always_and(spec, pre, p(0), lift_state(rr));
    // [](p(0) /\ rr) ~> [](q(0) /\ conjuncted_current_state_matches_vrs /\ old_vrs_set_is_owned_by_vd /\ icsm)
    esr_for_each_ranking(spec, vrs_set, vd, new_vrs_key);
    let r_pre = lift_state(conjuncted_desired_state_is_vrs(vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)));
    let r_post = lift_state(conjuncted_current_state_matches_vrs(vrs_set)).and(lift_state(old_vrs_set_is_owned_by_vd(vrs_set, vd, new_vrs_key)));
    leads_to_self(always(lift_state(icsm)));
    always_leads_to_always_and(spec, r_pre, lift_state(icsm), r_post, lift_state(icsm));
    temp_pred_equality(lift_state(rr), r_pre.and(lift_state(icsm)));
    assert(spec.entails(always(p(0)).leads_to(always(q(0)))));
    always_leads_to_always_and(spec, p(0), lift_state(rr), q(0), r_post.and(lift_state(icsm)));
    leads_to_trans(spec, pre, always(p(0).and(lift_state(rr))), always(q(0).and(r_post.and(lift_state(icsm)))));
    // Everything together implies composed_current_state_matches
    let q1 = q(0).and(r_post.and(lift_state(icsm)));
    assert(q1.and(lift_state(inv)).entails(lift_state(composed_current_state_matches(vd)))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] q1.and(lift_state(inv)).satisfied_by(ex)
            implies lift_state(composed_current_state_matches(vd)).satisfied_by(ex) by {
            conjuncted_current_state_matches_old_vrs_0_implies_composed(vd, cluster, controller_id, vrs_set, new_vrs, new_vrs_key, ex.head());
        }
    }
    leads_to_always_enhance(spec, lift_state(inv), pre, q1, lift_state(composed_current_state_matches(vd)));
}

// For a fixed new vrs key, []inductive_current_state_matches ~> []composed_current_state_matches
pub proof fn rolling_update_new_vrs_key_leads_to_composed_current_state_matches(
    spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs_key: ObjectRef
)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
        spec.entails(next_with_wf(cluster, controller_id)),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        spec.entails(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)),
    ensures
        spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))
            .leads_to(always(lift_state(composed_current_state_matches(vd))))),
{
    let icsm = lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key));
    let inv = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id));
    let post = always(lift_state(composed_current_state_matches(vd)));
    let witness_pred = |t: (VReplicaSetView, nat, Set<VReplicaSetView>)| rolling_update_witness_pred(vd, controller_id, new_vrs_key, t.0, t.1, t.2);
    // every witness leads to post
    assert forall |t: (VReplicaSetView, nat, Set<VReplicaSetView>)| #[trigger] spec.entails(witness_pred(t).leads_to(post)) by {
        rolling_update_witness_leads_to_composed_current_state_matches(spec, vd, controller_id, cluster, new_vrs_key, t.0, t.1, t.2);
    }
    leads_to_exists_intro(spec, witness_pred, post);
    // []icsm /\ inv implies some witness
    assert(always(icsm).and(inv).entails(tla_exists(witness_pred))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] always(icsm).and(inv).satisfied_by(ex)
            implies tla_exists(witness_pred).satisfied_by(ex) by {
            let s = ex.head();
            assert(icsm.satisfied_by(ex.suffix(0)));
            assert(ex.suffix(0).head() == s);
            assert(inductive_current_state_matches(vd, controller_id, new_vrs_key)(s));
            assert(cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s));
            let t = rolling_update_witness(vd, cluster, controller_id, new_vrs_key, s);
            assert(witness_pred(t).satisfied_by(ex));
        }
    }
    entails_implies_leads_to(spec, always(icsm).and(inv), tla_exists(witness_pred));
    leads_to_by_borrowing_inv(spec, always(icsm), tla_exists(witness_pred), inv);
    leads_to_trans(spec, always(icsm), tla_exists(witness_pred), post);
}

pub proof fn rolling_update_leads_to_composed_current_state_matches_vd(
    provided_spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster
)
    requires
        // environment invariants
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        // ESR for vrs
        provided_spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
        // ESR for vd (with rolling update behavior)
        provided_spec.entails(always(lift_state(desired_state_is(vd))).leads_to(tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))))),
        // vd rely
        provided_spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        provided_spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
        provided_spec.entails(always(lift_state(desired_state_is(vd))).leads_to(assumption_and_invariants_of_all_phases(vd, cluster, controller_id))),
    ensures
        provided_spec.entails(always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(composed_current_state_matches(vd))))),
{
    let desired = always(lift_state(desired_state_is(vd)));
    let post = always(lift_state(composed_current_state_matches(vd)));
    let key_to_p = |new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)));
    let vrs_esr = vrs_liveness::vrs_eventually_stable_reconciliation();
    let vd_esr = desired.leads_to(tla_exists(key_to_p));
    let rely = always(lifted_vd_rely_condition(cluster, controller_id));
    let interferes = always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id));
    let aai = assumption_and_invariants_of_all_phases(vd, cluster, controller_id);
    // stable_spec: the stable assumptions provided_spec directly entails
    let stable_spec = vrs_esr.and(vd_esr).and(rely).and(interferes);
    assert(valid(stable(vrs_esr))) by {
        let a_to_p = |vrs: VReplicaSetView| always(lift_state(vrs_liveness::desired_state_is(vrs)));
        let a_to_q = |vrs: VReplicaSetView| always(lift_state(vrs_liveness::current_state_matches(vrs)));
        tla_forall_a_p_a_leads_to_q_a_is_stable(a_to_p, a_to_q);
        tla_forall_p_tla_forall_q_equality(
            |vrs: VReplicaSetView| a_to_p(vrs).leads_to(a_to_q(vrs)),
            |vrs: VReplicaSetView| vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs)
        );
    }
    leads_to_is_stable(desired, tla_exists(key_to_p));
    always_p_is_stable(lifted_vd_rely_condition(cluster, controller_id));
    always_p_is_stable(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id));
    stable_and_n!(vrs_esr, vd_esr, rely, interferes);
    combine_spec_entails_n!(provided_spec, stable_spec, vrs_esr, vd_esr, rely, interferes);
    // spec: stable_spec together with the (stable) invariants of all phases
    let spec = stable_spec.and(aai);
    entails_trans(spec, stable_spec, vrs_esr);
    entails_trans(spec, stable_spec, vd_esr);
    entails_trans(spec, stable_spec, rely);
    entails_trans(spec, stable_spec, interferes);
    entails_trans(spec, aai, invariants(vd, cluster, controller_id));
    entails_trans(spec, invariants(vd, cluster, controller_id), next_with_wf(cluster, controller_id));
    entails_trans(spec, next_with_wf(cluster, controller_id), always(lift_action(cluster.next())));
    spec_entails_assumptions_and_invariants_of_all_phases_implies_cluster_invariants_since_reconciliation(spec, vd, cluster, controller_id);
    // for each new vrs key, []inductive_current_state_matches ~> post
    assert forall |new_vrs_key: ObjectRef| #[trigger] spec.entails(key_to_p(new_vrs_key).leads_to(post)) by {
        rolling_update_new_vrs_key_leads_to_composed_current_state_matches(spec, vd, controller_id, cluster, new_vrs_key);
    }
    leads_to_exists_intro(spec, key_to_p, post);
    leads_to_trans(spec, desired, tla_exists(key_to_p), post);
    // move aai back to the left of ~>
    assumption_and_invariants_of_all_phases_is_stable(vd, cluster, controller_id);
    unpack_conditions_from_spec(stable_spec, aai, desired, post);
    entails_trans(provided_spec, stable_spec, desired.and(aai).leads_to(post));
    // provided_spec |= []desired ~> []desired /\ aai
    leads_to_with_always(provided_spec, desired, aai, lift_state(desired_state_is(vd)));
    temp_pred_equality(desired.and(desired), desired);
    temp_pred_equality(aai.and(desired), desired.and(aai));
    leads_to_trans(provided_spec, desired, desired.and(aai), post);
}

}
