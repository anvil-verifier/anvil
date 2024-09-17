// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::v_replica_set_controller::{
    model::reconciler::*,
    proof::{
        helper_invariants,
        liveness::{resource_match::*, spec::*, terminate},
        predicate::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

// We prove init /\ []next /\ []wf |= []VReplicaSet::desired_state_is(vrs) ~> []current_state_matches(vrs) holds for each vrs.
proof fn liveness_proof_forall_vrs()
   ensures liveness_theorem(),
{
    assert forall |vrs: VReplicaSetView| #[trigger] cluster_spec().entails(liveness(vrs)) by {
        liveness_proof(vrs);
    };
    spec_entails_tla_forall(cluster_spec(), |vrs: VReplicaSetView| liveness(vrs));
}

proof fn liveness_proof(vrs: VReplicaSetView)
    ensures cluster_spec().entails(liveness(vrs)),
{
    assumption_and_invariants_of_all_phases_is_stable(vrs);
    lemma_true_leads_to_always_current_state_matches(vrs);
    reveal_with_fuel(spec_before_phase_n, 8);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(7, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(6, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(5, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(4, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(3, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(2, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(1, vrs);

    let assumption = always(lift_state(VRSCluster::desired_state_is(vrs)));
    unpack_conditions_from_spec(invariants(vrs), assumption, true_pred(), always(lift_state(current_state_matches(vrs))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    entails_trans(
        cluster_spec().and(derived_invariants_since_beginning(vrs)), invariants(vrs),
        always(lift_state(VRSCluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches(vrs))))
    );
    sm_spec_entails_all_invariants(vrs);
    simplify_predicate(cluster_spec(), derived_invariants_since_beginning(vrs));
}

#[verifier(external_body)]
proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, vrs: VReplicaSetView)
    requires
        1 <= i <= 7,
        valid(stable(spec_before_phase_n(i, vrs))),
        spec_before_phase_n(i + 1, vrs).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs)))))
    ensures spec_before_phase_n(i, vrs).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs))))),
{
}

proof fn lemma_true_leads_to_always_current_state_matches(vrs: VReplicaSetView)
    ensures assumption_and_invariants_of_all_phases(vrs).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs))))),
{
    let spec = assumption_and_invariants_of_all_phases(vrs);

    let reconcile_idle = lift_state(|s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) });
    let reconcile_scheduled = lift_state(|s: VRSCluster| {
        &&& !s.ongoing_reconciles().contains_key(vrs.object_ref())
        &&& s.scheduled_reconciles().contains_key(vrs.object_ref())
    });
    let at_init = lift_state(no_pending_req_at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init));
    let diff_at_init = |diff| lift_state(
        |s: VRSCluster| {
            &&& no_pending_req_at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, vrs);
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(vrs).

    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(spec, vrs);
    lemma_from_scheduled_to_init_step(spec, vrs);

    // Show that true == exists |diff| num_diff_pods_is(diff).
    assert_by(true_pred::<VRSCluster>() == tla_exists(|diff| lift_state(num_diff_pods_is(vrs, diff))), {
        let exists_num_diff_pods_is = tla_exists(|diff| lift_state(num_diff_pods_is(vrs, diff)));
        assert forall |ex: Execution<VRSCluster>|
        true_pred::<VRSCluster>().satisfied_by(ex) implies #[trigger] exists_num_diff_pods_is.satisfied_by(ex) by {
            let s = ex.head();
            let pods = matching_pods(vrs, s.resources());
            let diff = pods.len() - vrs.spec.replicas.unwrap_or(0);

            // Instantiate exists statement.
            assert((|diff| lift_state(num_diff_pods_is(vrs, diff)))(diff).satisfied_by(ex));
        }
        assert(valid(true_pred::<VRSCluster>().implies(exists_num_diff_pods_is)));
        temp_pred_equality(true_pred::<VRSCluster>(), tla_exists(|diff| lift_state(num_diff_pods_is(vrs, diff))));
    });

    // Show that init /\ no_pending_req ~> exists |diff| (num_diff_pods_is(diff) /\ init)
    assert_by(spec.entails(at_init.leads_to(tla_exists(diff_at_init))), {
        assert forall |ex: Execution<VRSCluster>|
        at_init.satisfied_by(ex) implies #[trigger] tla_exists(diff_at_init).satisfied_by(ex) by {
            assert(tla_exists(|diff| lift_state(num_diff_pods_is(vrs, diff))).satisfied_by(ex));
            let diff = choose |diff| lift_state(#[trigger] num_diff_pods_is(vrs, diff)).satisfied_by(ex);
            assert(diff_at_init(diff).satisfied_by(ex));
        }
        always_implies_to_leads_to(spec, at_init, tla_exists(diff_at_init));
    });

    // The following shows exists |diff| (num_diff_pods_is(diff) /\ init) ~> current_state_matches(vrs)
    assert forall |diff| #[trigger] spec.entails(diff_at_init(diff).leads_to(lift_state(current_state_matches(vrs)))) by {
        lemma_from_diff_and_init_to_current_state_matches(spec, vrs, diff);
    }
    leads_to_exists_intro(spec, diff_at_init, lift_state(current_state_matches(vrs)));

    // Chain everything together
    leads_to_trans_n!(
        spec,
        true_pred(),
        reconcile_idle,
        reconcile_scheduled,
        at_init,
        tla_exists(diff_at_init),
        lift_state(current_state_matches(vrs))
    );

    // Further prove stability
    lemma_current_state_matches_is_stable(spec, vrs, true_pred());
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<VRSCluster>, vrs: VReplicaSetView)
    requires
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::desired_state_is(vrs)))),
    ensures
        spec.entails(lift_state(|s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) })
        .leads_to(lift_state(|s: VRSCluster| {
            &&& !s.ongoing_reconciles().contains_key(vrs.object_ref())
            &&& s.scheduled_reconciles().contains_key(vrs.object_ref())
        }))),
{
    let pre = |s: VRSCluster| {
        &&& !s.ongoing_reconciles().contains_key(vrs.object_ref())
        &&& !s.scheduled_reconciles().contains_key(vrs.object_ref())
    };
    let post = |s: VRSCluster| {
        &&& !s.ongoing_reconciles().contains_key(vrs.object_ref())
        &&& s.scheduled_reconciles().contains_key(vrs.object_ref())
    };
    let input = vrs.object_ref();
    VRSCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(spec, input, VRSCluster::next(), VRSCluster::desired_state_is(vrs), pre, post);
    entails_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine(spec, lift_state(pre), lift_state(post), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: VRSCluster| {!s.ongoing_reconciles().contains_key(vrs.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<VRSCluster>, vrs: VReplicaSetView)
    requires
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(VRSCluster::the_object_in_schedule_has_spec_and_uid_as(vrs)))),
    ensures
        spec.entails(lift_state(|s: VRSCluster| {
            &&& !s.ongoing_reconciles().contains_key(vrs.object_ref())
            &&& s.scheduled_reconciles().contains_key(vrs.object_ref())
        }).leads_to(lift_state(no_pending_req_at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)))),
{
    let pre = |s: VRSCluster| {
        &&& !s.ongoing_reconciles().contains_key(vrs.object_ref())
        &&& s.scheduled_reconciles().contains_key(vrs.object_ref())
    };
    let post = no_pending_req_at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init);
    let input = (None, Some(vrs.object_ref()));
    let stronger_next = |s, s_prime| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::crash_disabled()(s)
        &&& VRSCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()(s)
        &&& VRSCluster::the_object_in_schedule_has_spec_and_uid_as(vrs)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(VRSCluster::next()),
        lift_state(VRSCluster::crash_disabled()),
        lift_state(VRSCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(VRSCluster::the_object_in_schedule_has_spec_and_uid_as(vrs))
    );
    VRSCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, VRSCluster::run_scheduled_reconcile(), pre, post);
}

}
