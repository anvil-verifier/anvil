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
use vstd::{prelude::*, set_lib::*, map_lib::*, multiset::*, utf8::*};
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
proof fn lemma_inductive_current_state_matches_preserves_during_api_server_step_on_other_msg(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs_key: ObjectRef, s: ClusterState, s_prime: ClusterState, msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s),
    vd_rely_condition(cluster, controller_id)(s),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s),
    s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()),
    msg.src != HostId::Controller(controller_id, vd.object_ref()),
ensures
    inductive_current_state_matches(vd, controller_id, new_vrs_key)(s_prime),
{
    hide(is_ascii_chars);
    let (uid, key) = choose |nv_uid_key: (Uid, ObjectRef)| {
        &&& #[trigger] etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), 0)(s)
    };
    let new_msgs = s_prime.in_flight().sub(s.in_flight());
    let local_state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let local_state_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    assert(local_state == local_state_prime);
    assert(s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0
        == s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0);
    VDeploymentReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();
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
            assert forall |i: int| #![trigger managed_vrs_list[i]] 0 <= i < managed_vrs_list.len() implies {
                let vrs = managed_vrs_list[i];
                let key = vrs.object_ref();
                let etcd_vrs = VReplicaSetView::unmarshal(s_prime.resources()[key])->Ok_0;
                &&& s_prime.resources().contains_key(key)
                &&& VReplicaSetView::unmarshal(s_prime.resources()[key]) is Ok
                &&& valid_owned_obj_key(vd, s_prime)(key)
                &&& etcd_vrs.metadata.without_resource_version() == vrs.metadata.without_resource_version()
                &&& etcd_vrs.spec == vrs.spec
            } by {
                let vrs = managed_vrs_list[i];
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
    hide(is_ascii_chars);
    let msg = input->0;
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
            lemma_inductive_current_state_matches_preserves_during_api_server_step_on_other_msg(
                vd, controller_id, cluster, new_vrs_key, s, s_prime, msg
            );
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
    assert(instantiated_etcd_state_is_with_zero_old_vrs_and_nv_key(vd, controller_id, new_vrs_key)(s)) by {
        lemma_esr_equiv_to_instantiated_etcd_state_is_with_nv_key(vd, cluster, controller_id, new_vrs_key, s);
    }
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
        } else if at_vd_step_with_vd(vd, controller_id, at_step![Init])(s) {
            // prove that the newly sent message has no response.
            if s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg is Some {
                let req_msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
                assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg));
                assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && msg != req_msg implies msg.rpc_id != req_msg.rpc_id by {
                    if !s.in_flight().contains(msg) {} // need this to invoke trigger.
                }
            }
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

// ranking predicate of iterative_esr: the new vrs is desired with its replicas diff away from vd, and vd stays reconciled
pub open spec fn desired_new_vrs_with_replicas_diff(vd: VDeploymentView, controller_id: int, new_vrs: VReplicaSetView, new_vrs_key: ObjectRef, diff: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, diff)(s)
        &&& inductive_current_state_matches(vd, controller_id, new_vrs_key)(s)
    }
}

// cluster.next() strengthened with the invariants that the inductive and ranking arguments rely on
pub open spec fn next_with_invariants(cluster: Cluster, vd: VDeploymentView, controller_id: int) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime)
        &&& vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
    }
}

proof fn lemma_always_next_with_invariants(
    spec: TempPred<ClusterState>, cluster: Cluster, vd: VDeploymentView, controller_id: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    ensures
        spec.entails(always(lift_action(next_with_invariants(cluster, vd, controller_id)))),
{
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)));
    combine_spec_entails_always_n!(spec,
        lift_action(next_with_invariants(cluster, vd, controller_id)),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)),
        later(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id),
        lifted_vd_rely_condition(cluster, controller_id)
    );
}

// spec |= [] conjuncted_desired_state_is_vrs ~> [] conjuncted_current_state_matches_vrs
proof fn lemma_conjuncted_vrs_esr(spec: TempPred<ClusterState>, vrs_set: Set<VReplicaSetView>)
    requires
        spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
    ensures
        spec.entails(always(lift_state(conjuncted_desired_state_is_vrs(vrs_set))).leads_to(always(lift_state(conjuncted_current_state_matches_vrs(vrs_set))))),
{
    let desired_state_is_vrs = |vrs| vrs_liveness::desired_state_is(vrs);
    let current_state_matches_vrs = |vrs| vrs_liveness::current_state_matches(vrs);
    assert forall |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) implies
        spec.entails(always(lift_state(desired_state_is_vrs(vrs))).leads_to(always(lift_state(current_state_matches_vrs(vrs))))) by {
        spec_entails_tla_forall_apply(spec, |vrs| vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs), vrs);
    }
    assert(conjuncted_desired_state_is_vrs(vrs_set)
        == |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> desired_state_is_vrs(vrs)(s)));
    assert(conjuncted_current_state_matches_vrs(vrs_set)
        == |s: ClusterState| (forall |vrs| #[trigger] vrs_set.contains(vrs) ==> current_state_matches_vrs(vrs)(s)));
    spec_entails_always_tla_forall_leads_to_always_tla_forall_within_domain(
        spec, desired_state_is_vrs, current_state_matches_vrs, vrs_set,
        conjuncted_desired_state_is_vrs(vrs_set), conjuncted_current_state_matches_vrs(vrs_set)
    );
}

// Ranking of iterative_esr never increases: returns the replicas diff of the new vrs in s_prime
proof fn lemma_new_vrs_replicas_diff_never_increases(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs: VReplicaSetView, n: nat, s: ClusterState, s_prime: ClusterState
) -> (m: nat)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        next_with_invariants(cluster, vd, controller_id)(s, s_prime),
        desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), n)(s),
        inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())(s),
    ensures
        m <= n,
        desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), m)(s_prime),
{
    let new_vrs_key = new_vrs.object_ref();
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            if msg.src == HostId::Controller(controller_id, vd.object_ref()) {
                if ru_req_msg_is_scale_new_vrs_by_one_req(vd, controller_id, msg)(s) {
                    let req = msg.content->APIRequest_0->GetThenUpdateRequest_0;
                    let req_vrs = VReplicaSetView::unmarshal(req.obj)->Ok_0;
                    assert(req.key() == new_vrs_key);
                    let new_vrs_prime = VReplicaSetView::unmarshal(s_prime.resources()[new_vrs_key])->Ok_0;
                    assert(get_replicas(new_vrs_prime.spec.replicas) == get_replicas(req_vrs.spec.replicas));
                    replicas_diff(vd, new_vrs_prime)
                } else {
                    // the only other pending request is the list request
                    assert(at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s));
                    assert(s_prime.resources() == s.resources());
                    n
                }
            } else {
                let obj = s.resources()[new_vrs_key];
                assert(s.resources().contains_key(new_vrs_key)); // trigger
                assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
                    // each_object_in_etcd_has_at_most_one_controller_owner
                    assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
                }
                lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(s, s_prime, vd, cluster, controller_id, msg);
                n
            }
        },
        _ => {
            assert(s_prime.resources() == s.resources());
            n
        }
    }
}

// Ranking of iterative_esr decreases: once the new vrs stably has diff > 0 replicas to go, the vd controller scales it
proof fn ranking_decreases_after_vrs_esr(
    spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs: VReplicaSetView, diff: nat
)
    requires
        diff > 0,
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
    ensures
        spec.entails(always(lift_state(desired_new_vrs_with_replicas_diff(vd, controller_id, new_vrs, new_vrs.object_ref(), diff))
            .and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff))))
            .leads_to(not(lift_state(desired_new_vrs_with_replicas_diff(vd, controller_id, new_vrs, new_vrs.object_ref(), diff))))),
{
    let desired_vrs = lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff));
    let inductive = lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref()));
    let current_vrs = lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff));
    let assumption = always(desired_vrs).and(always(inductive)).and(always(current_vrs));
    let post = not(desired_vrs.and(inductive));
    let stable_spec = assumption_and_invariants_of_all_phases(vd, cluster, controller_id)
        .and(always(lifted_vd_rely_condition(cluster, controller_id)))
        .and(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)));
    // stable_spec /\ assumption |= true ~> init ~> post
    assert(stable_spec.and(assumption).entails(true_pred().leads_to(post))) by {
        let composed_spec = stable_spec.and(assumption);
        let init = and!(
            at_vd_step_with_vd(vd, controller_id, at_step![Init]),
            no_pending_req_in_cluster(vd, controller_id)
        );
        spec_entails_assumptions_and_invariants_of_all_phases_implies_cluster_invariants_since_reconciliation(composed_spec, vd, cluster, controller_id);
        lemma_true_leads_to_init(vd, cluster, controller_id);
        entails_trans(composed_spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), true_pred().leads_to(lift_state(init)));
        lemma_from_init_to_not_desired_state_is(vd, composed_spec, cluster, controller_id, new_vrs, diff);
        leads_to_trans(composed_spec, true_pred(), lift_state(init), post);
    }
    assumption_and_invariants_of_all_phases_is_stable(vd, cluster, controller_id);
    always_p_is_stable(lifted_vd_rely_condition(cluster, controller_id));
    always_p_is_stable(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id));
    stable_and_n!(
        assumption_and_invariants_of_all_phases(vd, cluster, controller_id),
        always(lifted_vd_rely_condition(cluster, controller_id)),
        always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))
    );
    unpack_conditions_from_spec(stable_spec, assumption, true_pred(), post);
    temp_pred_equality(true_pred().and(assumption), assumption);
    entails_and_n!(spec,
        assumption_and_invariants_of_all_phases(vd, cluster, controller_id),
        always(lifted_vd_rely_condition(cluster, controller_id)),
        always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))
    );
    entails_trans(spec, stable_spec, assumption.leads_to(post));
    always_and_equality_n!(desired_vrs, inductive, current_vrs);
    temp_pred_equality(
        lift_state(desired_new_vrs_with_replicas_diff(vd, controller_id, new_vrs, new_vrs.object_ref(), diff)),
        desired_vrs.and(inductive)
    );
}

// iterative_esr on the new vrs ranked by replicas_diff: the new vrs eventually stably matches the vd replicas
proof fn lemma_new_vrs_eventually_matches_vd_replicas(
    spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs: VReplicaSetView
)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(always(lift_action(next_with_invariants(cluster, vd, controller_id)))),
        spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
        spec.entails(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
    ensures
        spec.entails(lift_state(desired_new_vrs_with_replicas_diff(vd, controller_id, new_vrs, new_vrs.object_ref(), replicas_diff(vd, new_vrs)))
            .leads_to(always(lift_state(desired_new_vrs_with_replicas_diff(vd, controller_id, new_vrs, new_vrs.object_ref(), 0))
                .and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), 0)))))),
{
    let p = |n: nat| desired_new_vrs_with_replicas_diff(vd, controller_id, new_vrs, new_vrs.object_ref(), n);
    let lifted_p = |n: nat| lift_state(p(n));
    let q = |n: nat| lifted_p(n).and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), n)));
    // VRS ESR at each rank
    assert forall |n: nat| #![trigger lifted_p(n)] spec.entails(always(lifted_p(n)).leads_to(always(q(n)))) by {
        let vrs = new_vrs.with_spec(new_vrs.spec.with_replicas(
            if get_replicas(vd.spec.replicas) > get_replicas(new_vrs.spec.replicas) {
                get_replicas(vd.spec.replicas) - n
            } else {
                get_replicas(vd.spec.replicas) + n
            }
        ));
        spec_entails_tla_forall_apply(spec, |vrs| vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs), vrs);
        leads_to_self(always(lifted_p(n)));
        always_leads_to_always_and(spec,
            lift_state(vrs_liveness::desired_state_is(vrs)), lifted_p(n),
            lift_state(vrs_liveness::current_state_matches(vrs)), lifted_p(n)
        );
        temp_pred_equality(lift_state(vrs_liveness::desired_state_is(vrs)).and(lifted_p(n)), lifted_p(n));
        temp_pred_equality(lift_state(vrs_liveness::current_state_matches(vrs)).and(lifted_p(n)), q(n));
    }
    // rank never increases
    assert forall |n: nat| #![trigger p(n)] forall |s, s_prime| #[trigger] next_with_invariants(cluster, vd, controller_id)(s, s_prime) && p(n)(s)
        ==> exists |m: nat| m <= n && #[trigger] p(m)(s_prime) by {
        assert forall |s, s_prime| #[trigger] next_with_invariants(cluster, vd, controller_id)(s, s_prime) && p(n)(s)
            implies exists |m: nat| m <= n && #[trigger] p(m)(s_prime) by {
            let m = lemma_new_vrs_replicas_diff_never_increases(vd, controller_id, cluster, new_vrs, n, s, s_prime);
            lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_with_nv_key(vd, controller_id, cluster, new_vrs.object_ref(), s, s_prime);
            assert(p(m)(s_prime));
        }
    }
    next_monotonic_to_always_exists(spec, next_with_invariants(cluster, vd, controller_id), p);
    assert forall |n: nat| #![trigger lifted_p(n)] spec.entails(always(lifted_p(n).implies(always(tla_exists(|m: nat| lift_state(|s| m <= n).and(lifted_p(m))))))) by {
        tla_exists_p_tla_exists_q_equality(|m: nat| lift_state(|s| m <= n).and(lift_state(p(m))), |m: nat| lift_state(|s| m <= n).and(lifted_p(m)));
        assert(spec.entails(always(lift_state(p(n)).implies(always(tla_exists(|m: nat| lift_state(|s| m <= n).and(lift_state(p(m)))))))));
    }
    // rank decreases
    assert forall |n: nat| #![trigger lifted_p(n)] n > 0 implies spec.entails(always(q(n)).leads_to(not(lifted_p(n)))) by {
        ranking_decreases_after_vrs_esr(spec, vd, controller_id, cluster, new_vrs, n);
    }
    iterative_esr(spec, lifted_p, q);
    let diff = replicas_diff(vd, new_vrs);
    assert(spec.entails(lifted_p(diff).leads_to(always(lifted_p(0)))));
    leads_to_trans(spec, lifted_p(diff), always(lifted_p(0)), always(q(0)));
}

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

// spec |= [] inductive_current_state_matches ~> [] composed_current_state_matches
proof fn lemma_always_inductive_current_state_matches_leads_to_always_composed_current_state_matches(
    spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs_key: ObjectRef
)
    requires
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)),
        spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
        spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
        spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
    ensures
        spec.entails(always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key))).leads_to(always(lift_state(composed_current_state_matches(vd))))),
{
    let always_inductive = always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)));
    let inv = cluster_invariants_since_reconciliation(cluster, vd, controller_id);
    spec_entails_assumptions_and_invariants_of_all_phases_implies_cluster_invariants_since_reconciliation(spec, vd, cluster, controller_id);
    entails_trans(spec, assumption_and_invariants_of_all_phases(vd, cluster, controller_id), always(lift_action(cluster.next())));
    lemma_always_next_with_invariants(spec, cluster, vd, controller_id);

    // old vrs track: [] inductive ~> \E old_vrs_set. [] old_vrs_post(old_vrs_set)
    let old_vrs_pre = |old_vrs_set| and!(
        conjuncted_desired_state_is_vrs(old_vrs_set),
        old_vrs_set_is_owned_by_vd(old_vrs_set, vd, new_vrs_key),
        inductive_current_state_matches(vd, controller_id, new_vrs_key)
    );
    let old_vrs_post = |old_vrs_set| lift_state(conjuncted_current_state_matches_vrs(old_vrs_set)).and(lift_state(old_vrs_pre(old_vrs_set)));
    assert(spec.entails(always_inductive.leads_to(tla_exists(|old_vrs_set| lift_state(old_vrs_pre(old_vrs_set)))))) by {
        assert forall |ex| #[trigger] always_inductive.and(lift_state(inv)).satisfied_by(ex)
            implies tla_exists(|old_vrs_set| lift_state(old_vrs_pre(old_vrs_set))).satisfied_by(ex) by {
            assert(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)).satisfied_by(ex.suffix(0)));
            let old_vrs_set = current_state_match_vd_implies_exists_old_vrs_set(vd, cluster, controller_id, new_vrs_key, ex.head());
            assert((|old_vrs_set| lift_state(old_vrs_pre(old_vrs_set)))(old_vrs_set).satisfied_by(ex));
        }
        entails_implies_leads_to(spec, always_inductive.and(lift_state(inv)), tla_exists(|old_vrs_set| lift_state(old_vrs_pre(old_vrs_set))));
        leads_to_by_borrowing_inv(spec, always_inductive, tla_exists(|old_vrs_set| lift_state(old_vrs_pre(old_vrs_set))), lift_state(inv));
    }
    assert forall |s, s_prime| (forall |old_vrs_set| #[trigger] old_vrs_pre(old_vrs_set)(s) && #[trigger] next_with_invariants(cluster, vd, controller_id)(s, s_prime) ==> old_vrs_pre(old_vrs_set)(s_prime)) by {
        assert forall |old_vrs_set| #[trigger] old_vrs_pre(old_vrs_set)(s) && next_with_invariants(cluster, vd, controller_id)(s, s_prime) implies old_vrs_pre(old_vrs_set)(s_prime) by {
            lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_with_nv_key(vd, controller_id, cluster, new_vrs_key, s, s_prime);
            composed_old_vrs_set_pre_preserves_from_s_to_s_prime(vd, controller_id, cluster, old_vrs_set, new_vrs_key, s, s_prime);
        }
    }
    leads_to_exists_stable(spec, next_with_invariants(cluster, vd, controller_id), always_inductive, old_vrs_pre);
    assert forall |old_vrs_set| #[trigger] spec.entails(always(lift_state(old_vrs_pre(old_vrs_set))).leads_to(always(old_vrs_post(old_vrs_set)))) by {
        lemma_conjuncted_vrs_esr(spec, old_vrs_set);
        leads_to_self(always(lift_state(old_vrs_pre(old_vrs_set))));
        always_leads_to_always_and(spec,
            lift_state(conjuncted_desired_state_is_vrs(old_vrs_set)), lift_state(old_vrs_pre(old_vrs_set)),
            lift_state(conjuncted_current_state_matches_vrs(old_vrs_set)), lift_state(old_vrs_pre(old_vrs_set))
        );
        temp_pred_equality(lift_state(conjuncted_desired_state_is_vrs(old_vrs_set)).and(lift_state(old_vrs_pre(old_vrs_set))), lift_state(old_vrs_pre(old_vrs_set)));
    }
    leads_to_exists_pointwise(spec, |old_vrs_set| always(lift_state(old_vrs_pre(old_vrs_set))), |old_vrs_set| always(old_vrs_post(old_vrs_set)));
    leads_to_trans(spec,
        always_inductive,
        tla_exists(|old_vrs_set| always(lift_state(old_vrs_pre(old_vrs_set)))),
        tla_exists(|old_vrs_set| always(old_vrs_post(old_vrs_set)))
    );

    // new vrs track: [] inductive ~> \E new_vrs. [] new_vrs_post(new_vrs)
    let new_vrs_pre = |new_vrs: VReplicaSetView| lift_state(desired_new_vrs_with_replicas_diff(vd, controller_id, new_vrs, new_vrs_key, replicas_diff(vd, new_vrs)));
    let new_vrs_post = |new_vrs: VReplicaSetView| lift_state(desired_new_vrs_with_replicas_diff(vd, controller_id, new_vrs, new_vrs_key, 0)).and(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs_key, 0)));
    assert(spec.entails(always_inductive.leads_to(tla_exists(new_vrs_pre)))) by {
        assert forall |ex| #[trigger] always_inductive.and(lift_state(inv)).satisfied_by(ex) implies tla_exists(new_vrs_pre).satisfied_by(ex) by {
            assert(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)).satisfied_by(ex.suffix(0)));
            // witness: the new vrs in etcd
            let etcd_vrs = VReplicaSetView::unmarshal(ex.head().resources()[new_vrs_key])->Ok_0;
            assert(etcd_vrs.metadata.owner_references->0.filter(controller_owner_filter()).len() == 1) by {
                assert(etcd_vrs.metadata.owner_references->0.filter(controller_owner_filter()).len() <= 1);
                assert(etcd_vrs.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
            }
            assert(new_vrs_pre(etcd_vrs).satisfied_by(ex));
        }
        entails_implies_leads_to(spec, always_inductive.and(lift_state(inv)), tla_exists(new_vrs_pre));
        leads_to_by_borrowing_inv(spec, always_inductive, tla_exists(new_vrs_pre), lift_state(inv));
    }
    assert forall |new_vrs: VReplicaSetView| #[trigger] spec.entails(new_vrs_pre(new_vrs).leads_to(always(new_vrs_post(new_vrs)))) by {
        if new_vrs.object_ref() == new_vrs_key {
            lemma_new_vrs_eventually_matches_vd_replicas(spec, vd, controller_id, cluster, new_vrs);
        } else {
            temp_pred_equality(new_vrs_pre(new_vrs), false_pred());
            false_leads_to_anything(spec, always(new_vrs_post(new_vrs)));
        }
    }
    leads_to_exists_pointwise(spec, new_vrs_pre, |new_vrs| always(new_vrs_post(new_vrs)));
    leads_to_trans(spec, always_inductive, tla_exists(new_vrs_pre), tla_exists(|new_vrs| always(new_vrs_post(new_vrs))));

    // \E old_vrs_set, new_vrs. [] old_vrs_post /\ [] new_vrs_post ~> [] composed_current_state_matches
    leads_to_exists_always_and_exists(spec, always_inductive, old_vrs_post, new_vrs_post);
    let all_vrs_post = |ov_set_nv: (Set<VReplicaSetView>, VReplicaSetView)| always(old_vrs_post(ov_set_nv.0)).and(always(new_vrs_post(ov_set_nv.1)));
    assert forall |ov_set_nv: (Set<VReplicaSetView>, VReplicaSetView)| #[trigger] spec.entails(all_vrs_post(ov_set_nv).leads_to(always(lift_state(composed_current_state_matches(vd))))) by {
        let vrs_post = old_vrs_post(ov_set_nv.0).and(new_vrs_post(ov_set_nv.1));
        always_and_equality(old_vrs_post(ov_set_nv.0), new_vrs_post(ov_set_nv.1));
        leads_to_self(always(vrs_post));
        assert forall |ex| #[trigger] vrs_post.and(lift_state(inv)).satisfied_by(ex) implies lift_state(composed_current_state_matches(vd)).satisfied_by(ex) by {
            conjuncted_current_state_matches_old_vrs_0_implies_composed(vd, cluster, controller_id, ov_set_nv.0, ov_set_nv.1, new_vrs_key, ex.head());
        }
        leads_to_always_enhance(spec, lift_state(inv), all_vrs_post(ov_set_nv), vrs_post, lift_state(composed_current_state_matches(vd)));
    }
    leads_to_exists_intro(spec, all_vrs_post, always(lift_state(composed_current_state_matches(vd))));
    leads_to_trans(spec, always_inductive, tla_exists(all_vrs_post), always(lift_state(composed_current_state_matches(vd))));
}

// *** Top-level rolling update ESR composition theorem ***
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
    let desired_vd = always(lift_state(desired_state_is(vd)));
    let composed_vd = always(lift_state(composed_current_state_matches(vd)));
    let aip = assumption_and_invariants_of_all_phases(vd, cluster, controller_id);
    let always_inductive = |new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)));
    let vd_esr = desired_vd.leads_to(tla_exists(always_inductive));
    // the stable part of provided_spec, which eventually holds together with aip
    let stable_spec = vd_esr
        .and(vrs_liveness::vrs_eventually_stable_reconciliation())
        .and(always(lifted_vd_rely_condition(cluster, controller_id)))
        .and(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)))
        .and(desired_vd.leads_to(aip));
    entails_and_n!(provided_spec,
        vd_esr,
        vrs_liveness::vrs_eventually_stable_reconciliation(),
        always(lifted_vd_rely_condition(cluster, controller_id)),
        always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)),
        desired_vd.leads_to(aip)
    );
    assert(valid(stable(stable_spec))) by {
        let desired_vrs = |vrs| always(lift_state(vrs_liveness::desired_state_is(vrs)));
        let current_vrs = |vrs| always(lift_state(vrs_liveness::current_state_matches(vrs)));
        tla_forall_a_p_a_leads_to_q_a_is_stable(desired_vrs, current_vrs);
        tla_forall_p_tla_forall_q_equality(|vrs| vrs_liveness::vrs_eventually_stable_reconciliation_per_cr(vrs), |vrs| desired_vrs(vrs).leads_to(current_vrs(vrs)));
        leads_to_is_stable(desired_vd, tla_exists(always_inductive));
        always_p_is_stable(lifted_vd_rely_condition(cluster, controller_id));
        always_p_is_stable(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id));
        leads_to_is_stable(desired_vd, aip);
        stable_and_n!(
            vd_esr,
            vrs_liveness::vrs_eventually_stable_reconciliation(),
            always(lifted_vd_rely_condition(cluster, controller_id)),
            always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id)),
            desired_vd.leads_to(aip)
        );
    }
    let spec = stable_spec.and(aip);
    assert forall |new_vrs_key: ObjectRef| spec.entails(always(lift_state(#[trigger] inductive_current_state_matches(vd, controller_id, new_vrs_key))).leads_to(composed_vd)) by {
        lemma_always_inductive_current_state_matches_leads_to_always_composed_current_state_matches(spec, vd, controller_id, cluster, new_vrs_key);
    }
    leads_to_exists_intro(spec, always_inductive, composed_vd);
    leads_to_trans(spec, desired_vd, tla_exists(always_inductive), composed_vd);
    // stable_spec |= [] desired_state_is ~> [] desired_state_is /\ aip ~> [] composed_current_state_matches
    unpack_conditions_from_spec(stable_spec, aip, desired_vd, composed_vd);
    assumption_and_invariants_of_all_phases_is_stable(vd, cluster, controller_id);
    stable_to_always(aip);
    leads_to_self(desired_vd);
    leads_to_always_and(stable_spec, desired_vd, lift_state(desired_state_is(vd)), aip);
    leads_to_trans(stable_spec, desired_vd, desired_vd.and(aip), composed_vd);
    entails_trans(provided_spec, stable_spec, desired_vd.leads_to(composed_vd));
}

}
