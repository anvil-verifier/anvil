// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants,
        liveness::{resource_match::*, spec::*, terminate},
        predicate::*,
        resource::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
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
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

// We prove init /\ []next /\ []wf |= []desired_state_is(fbc) ~> []current_state_matches(fbc) holds for each fbc.
proof fn liveness_proof_forall_fbc()
    ensures liveness_theorem::<FluentBitConfigMaker>(),
{
    assert forall |fbc: FluentBitConfigView| #[trigger] cluster_spec().entails(liveness::<FluentBitConfigMaker>(fbc)) by {
        liveness_proof(fbc);
    };
    spec_entails_tla_forall(cluster_spec(), |fbc: FluentBitConfigView| liveness::<FluentBitConfigMaker>(fbc));
}

proof fn liveness_proof(fbc: FluentBitConfigView)
    ensures cluster_spec().entails(liveness::<FluentBitConfigMaker>(fbc)),
{
    assumption_and_invariants_of_all_phases_is_stable(fbc);
    lemma_true_leads_to_always_current_state_matches(fbc);
    reveal_with_fuel(spec_before_phase_n, 7);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(6, fbc);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(5, fbc);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(4, fbc);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(3, fbc);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(2, fbc);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(1, fbc);

    let assumption = always(lift_state(desired_state_is(fbc)));
    unpack_conditions_from_spec(invariants(fbc), assumption, true_pred(), always(lift_state(current_state_matches::<FluentBitConfigMaker>(fbc))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    valid_implies_trans(
        cluster_spec().and(derived_invariants_since_beginning(fbc)), invariants(fbc),
        always(lift_state(desired_state_is(fbc))).leads_to(always(lift_state(current_state_matches::<FluentBitConfigMaker>(fbc))))
    );
    sm_spec_entails_all_invariants(fbc);
    simplify_predicate(cluster_spec(), derived_invariants_since_beginning(fbc));
}

proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, fbc: FluentBitConfigView)
    requires
        1 <= i <= 6,
        valid(stable(spec_before_phase_n(i, fbc))),
        spec_before_phase_n(i + 1, fbc).entails(true_pred().leads_to(always(lift_state(current_state_matches::<FluentBitConfigMaker>(fbc)))))
    ensures spec_before_phase_n(i, fbc).entails(true_pred().leads_to(always(lift_state(current_state_matches::<FluentBitConfigMaker>(fbc))))),
{
    reveal_with_fuel(spec_before_phase_n, 7);
    temp_pred_equality(spec_before_phase_n(i + 1, fbc), spec_before_phase_n(i, fbc).and(invariants_since_phase_n(i, fbc)));
    spec_of_previous_phases_entails_eventually_new_invariants(i, fbc);
    unpack_conditions_from_spec(spec_before_phase_n(i, fbc), invariants_since_phase_n(i, fbc), true_pred(), always(lift_state(current_state_matches::<FluentBitConfigMaker>(fbc))));
    temp_pred_equality(true_pred().and(invariants_since_phase_n(i, fbc)), invariants_since_phase_n(i, fbc));
    leads_to_trans_temp(spec_before_phase_n(i, fbc), true_pred(), invariants_since_phase_n(i, fbc), always(lift_state(current_state_matches::<FluentBitConfigMaker>(fbc))));
}

proof fn lemma_true_leads_to_always_current_state_matches(fbc: FluentBitConfigView)
    ensures assumption_and_invariants_of_all_phases(fbc).entails(true_pred().leads_to(always(lift_state(current_state_matches::<FluentBitConfigMaker>(fbc))))),
{
    let spec = assumption_and_invariants_of_all_phases(fbc);
    lemma_true_leads_to_always_state_matches_for_all_resources(fbc);
    let a_to_p = |res: SubResource| lift_state(sub_resource_state_matches(res, fbc));
    helper_invariants::leads_to_always_tla_forall_subresource(spec, true_pred(), a_to_p);
    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies lift_state(current_state_matches::<FluentBitConfigMaker>(fbc)).satisfied_by(ex) by {
        let s = ex.head();
        assert forall |res: SubResource| #[trigger] resource_state_matches::<FluentBitConfigMaker>(res, fbc, s.resources()) by {
            tla_forall_apply(a_to_p, res);
            assert(a_to_p(res).satisfied_by(ex));
            assert(sub_resource_state_matches(res, fbc)(s));
        }
    }
    temp_pred_equality(tla_forall(|res: SubResource| lift_state(sub_resource_state_matches(res, fbc))), lift_state(current_state_matches::<FluentBitConfigMaker>(fbc)));
}

proof fn lemma_true_leads_to_always_state_matches_for_all_resources(fbc: FluentBitConfigView)
    ensures forall |sub_resource: SubResource| assumption_and_invariants_of_all_phases(fbc).entails(true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, fbc))))),
{
    let spec = assumption_and_invariants_of_all_phases(fbc);

    assert forall |action: ActionKind, sub_resource: SubResource| #![auto] spec.entails(always(lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(action, sub_resource)))))) by {
        always_tla_forall_apply(spec, |step: (ActionKind, SubResource)| lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1)))), (action, sub_resource));
    }

    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, fbc);
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(fbc).

    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(spec, fbc);
    lemma_from_scheduled_to_init_step(spec, fbc);

    // After applying this lemma, we get spec |= init /\ no_pending_req ~> get_service_account /\ pending_req.
    lemma_from_init_step_to_after_get_secret_step(spec, fbc);

    always_tla_forall_apply_for_sub_resource(spec, SubResource::Secret, fbc);
    lemma_from_after_get_resource_step_to_resource_matches(spec, fbc, SubResource::Secret);
    leads_to_trans_n!(
        spec, true_pred(), lift_state(|s: FBCCluster| { !s.ongoing_reconciles().contains_key(fbc.object_ref()) }),
        lift_state(|s: FBCCluster| { !s.ongoing_reconciles().contains_key(fbc.object_ref()) && s.scheduled_reconciles().contains_key(fbc.object_ref())}),
        lift_state(no_pending_req_at_fbc_step_with_fbc(fbc, FluentBitConfigReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Secret, fbc)),
        lift_state(sub_resource_state_matches(SubResource::Secret, fbc))
    );
    lemma_resource_object_is_stable(spec, SubResource::Secret, fbc, true_pred());
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fbc)))),
    ensures
        spec.entails(lift_state(|s: FBCCluster| { !s.ongoing_reconciles().contains_key(fbc.object_ref()) }).leads_to(lift_state(|s: FBCCluster| {
            &&& !s.ongoing_reconciles().contains_key(fbc.object_ref())
            &&& s.scheduled_reconciles().contains_key(fbc.object_ref())}))),
{
    let pre = |s: FBCCluster| {
        &&& !s.ongoing_reconciles().contains_key(fbc.object_ref())
        &&& !s.scheduled_reconciles().contains_key(fbc.object_ref())
    };
    let post = |s: FBCCluster| {
        &&& !s.ongoing_reconciles().contains_key(fbc.object_ref())
        &&& s.scheduled_reconciles().contains_key(fbc.object_ref())
    };
    let input = fbc.object_ref();
    FBCCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(spec, input, FBCCluster::next(), desired_state_is(fbc), pre, post);
    valid_implies_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine_temp(spec, lift_state(pre), lift_state(post), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: FBCCluster| {!s.ongoing_reconciles().contains_key(fbc.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::the_object_in_schedule_has_spec_and_uid_as(fbc)))),
    ensures
        spec.entails(lift_state(|s: FBCCluster| {
            &&& !s.ongoing_reconciles().contains_key(fbc.object_ref())
            &&& s.scheduled_reconciles().contains_key(fbc.object_ref())
        }).leads_to(lift_state(no_pending_req_at_fbc_step_with_fbc(fbc, FluentBitConfigReconcileStep::Init)))),
{
    let pre = |s: FBCCluster| {
        &&& !s.ongoing_reconciles().contains_key(fbc.object_ref())
        &&& s.scheduled_reconciles().contains_key(fbc.object_ref())
    };
    let post = no_pending_req_at_fbc_step_with_fbc(fbc, FluentBitConfigReconcileStep::Init);
    let input = (None, Some(fbc.object_ref()));
    let stronger_next = |s, s_prime| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()(s)
        &&& FBCCluster::the_object_in_schedule_has_spec_and_uid_as(fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(FBCCluster::the_object_in_schedule_has_spec_and_uid_as(fbc))
    );
    FBCCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, FBCCluster::run_scheduled_reconcile(), pre, post);
}

proof fn lemma_from_init_step_to_after_get_secret_step(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
    ensures spec.entails(lift_state(no_pending_req_at_fbc_step_with_fbc(fbc, FluentBitConfigReconcileStep::Init)).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Secret, fbc)))),
{
    let pre = no_pending_req_at_fbc_step_with_fbc(fbc, FluentBitConfigReconcileStep::Init);
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::Secret, fbc);
    let input = (None, Some(fbc.object_ref()));
    let stronger_next = |s, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(FBCCluster::next()), lift_state(FBCCluster::crash_disabled())
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| FBCCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.1.get_Some_0() != fbc.object_ref() {
                    assert(pre(s_prime));
                } else {
                    assert(post(s_prime));
                }
            },
            _ => {
                assert(pre(s_prime));
            }
        }
    }
    FBCCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, FBCCluster::continue_reconcile(), pre, post);
}

proof fn always_tla_forall_apply_for_sub_resource(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, fbc))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, fbc))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight(res, fbc))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(res, fbc))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, fbc))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, fbc))))),
    ensures
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc)))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, fbc)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, fbc)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight(res, fbc)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(res, fbc)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, fbc)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, fbc)), sub_resource);
}

}
