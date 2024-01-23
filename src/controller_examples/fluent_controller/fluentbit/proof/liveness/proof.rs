// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants,
        liveness::{
            daemon_set_match::{
                lemma_daemon_set_is_stable,
                lemma_from_after_get_daemon_set_step_to_daemon_set_matches,
            },
            resource_match::*,
            spec::*,
            terminate,
        },
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

// We prove init /\ []next /\ []wf |= []desired_state_is(fb) ~> []current_state_matches(fb) holds for each fb.
proof fn liveness_proof_forall_fb()
    ensures liveness_theorem::<FluentBitMaker>(),
{
    assert forall |fb: FluentBitView| #[trigger] cluster_spec().entails(liveness::<FluentBitMaker>(fb)) by {
        liveness_proof(fb);
    };
    spec_entails_tla_forall(cluster_spec(), |fb: FluentBitView| liveness::<FluentBitMaker>(fb));
}

proof fn liveness_proof(fb: FluentBitView)
    ensures cluster_spec().entails(liveness::<FluentBitMaker>(fb)),
{
    assumption_and_invariants_of_all_phases_is_stable(fb);
    lemma_true_leads_to_always_current_state_matches(fb);
    reveal_with_fuel(spec_before_phase_n, 8);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(7, fb);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(6, fb);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(5, fb);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(4, fb);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(3, fb);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(2, fb);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(1, fb);

    let assumption = always(lift_state(desired_state_is(fb)));
    unpack_conditions_from_spec(invariants(fb), assumption, true_pred(), always(lift_state(current_state_matches::<FluentBitMaker>(fb))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    valid_implies_trans(
        cluster_spec().and(derived_invariants_since_beginning(fb)), invariants(fb),
        always(lift_state(desired_state_is(fb))).leads_to(always(lift_state(current_state_matches::<FluentBitMaker>(fb))))
    );
    sm_spec_entails_all_invariants(fb);
    simplify_predicate(cluster_spec(), derived_invariants_since_beginning(fb));
}

proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, fb: FluentBitView)
    requires
        1 <= i <= 7,
        valid(stable(spec_before_phase_n(i, fb))),
        spec_before_phase_n(i + 1, fb).entails(true_pred().leads_to(always(lift_state(current_state_matches::<FluentBitMaker>(fb)))))
    ensures spec_before_phase_n(i, fb).entails(true_pred().leads_to(always(lift_state(current_state_matches::<FluentBitMaker>(fb))))),
{
    reveal_with_fuel(spec_before_phase_n, 8);
    temp_pred_equality(spec_before_phase_n(i + 1, fb), spec_before_phase_n(i, fb).and(invariants_since_phase_n(i, fb)));
    spec_of_previous_phases_entails_eventually_new_invariants(i, fb);
    unpack_conditions_from_spec(spec_before_phase_n(i, fb), invariants_since_phase_n(i, fb), true_pred(), always(lift_state(current_state_matches::<FluentBitMaker>(fb))));
    temp_pred_equality(true_pred().and(invariants_since_phase_n(i, fb)), invariants_since_phase_n(i, fb));
    leads_to_trans_temp(spec_before_phase_n(i, fb), true_pred(), invariants_since_phase_n(i, fb), always(lift_state(current_state_matches::<FluentBitMaker>(fb))));
}

proof fn lemma_true_leads_to_always_current_state_matches(fb: FluentBitView)
    ensures assumption_and_invariants_of_all_phases(fb).entails(true_pred().leads_to(always(lift_state(current_state_matches::<FluentBitMaker>(fb))))),
{
    let spec = assumption_and_invariants_of_all_phases(fb);
    lemma_true_leads_to_always_state_matches_for_all_resources(fb);
    let a_to_p = |res: SubResource| lift_state(sub_resource_state_matches(res, fb));
    helper_invariants::leads_to_always_tla_forall_subresource(spec, true_pred(), a_to_p);
    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies lift_state(current_state_matches::<FluentBitMaker>(fb)).satisfied_by(ex) by {
        let s = ex.head();
        assert forall |res: SubResource| #[trigger] resource_state_matches::<FluentBitMaker>(res, fb, s.resources()) by {
            tla_forall_apply(a_to_p, res);
            assert(a_to_p(res).satisfied_by(ex));
            assert(sub_resource_state_matches(res, fb)(s));
        }
    }
    temp_pred_equality(tla_forall(|res: SubResource| lift_state(sub_resource_state_matches(res, fb))), lift_state(current_state_matches::<FluentBitMaker>(fb)));
}

proof fn lemma_true_leads_to_always_state_matches_for_all_resources(fb: FluentBitView)
    ensures forall |sub_resource: SubResource| assumption_and_invariants_of_all_phases(fb).entails(true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, fb))))),
{
    let spec = assumption_and_invariants_of_all_phases(fb);

    assert forall |action: ActionKind, sub_resource: SubResource| #![auto] spec.entails(always(lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(action, sub_resource)))))) by {
        always_tla_forall_apply(spec, |step: (ActionKind, SubResource)| lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(step.0, step.1)))), (action, sub_resource));
    }

    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, fb);
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(fb).

    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(spec, fb);
    lemma_from_scheduled_to_init_step(spec, fb);

    // After applying this lemma, we get spec |= init /\ no_pending_req ~> get_service_account /\ pending_req.
    lemma_from_init_step_to_after_get_service_account_step(spec, fb);

    // We first show that the reconciler can go to at_after_get_resource_step(next_resource) from at_after_get_resource_step(sub_resource)
    // where sub_resource cannot be DaemonSet because it's the last resource to be processed and doesn't have its next_resource.
    // Through this, we can string all the resources together in sequence. This also means that the system can go to any
    // at_after_get_resource_step(sub_resource) from an arbitrary state.
    assert forall |sub_resource: SubResource| sub_resource != SubResource::DaemonSet implies
    spec.entails(
        lift_state(#[trigger] pending_req_in_flight_at_after_get_resource_step(sub_resource, fb))
            .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource).get_AfterKRequestStep_1(), fb)))
    ) by {
        always_tla_forall_apply_for_sub_resource(spec, sub_resource, fb);
        let next_resource = next_resource_after(sub_resource).get_AfterKRequestStep_1();
        lemma_from_after_get_resource_step_to_resource_matches(spec, fb, sub_resource, next_resource);
    }
    // Thanks to the recursive construction of macro.
    leads_to_trans_n!(
        spec, true_pred(), lift_state(|s: FBCluster| { !s.ongoing_reconciles().contains_key(fb.object_ref()) }),
        lift_state(|s: FBCluster| { !s.ongoing_reconciles().contains_key(fb.object_ref()) && s.scheduled_reconciles().contains_key(fb.object_ref())}),
        lift_state(no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Role, fb)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::RoleBinding, fb)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Service, fb)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::DaemonSet, fb))
    );

    // Since we already have true ~> at_after_get_resource_step(sub_resource), and we can get at_after_get_resource_step(sub_resource)
    // ~> sub_resource_state_matches(sub_resource, fb) by applying lemma lemma_from_after_get_resource_step_to_resource_matches,
    // we now have true ~> sub_resource_state_matches(sub_resource, fb).
    assert forall |sub_resource: SubResource| spec.entails(
        true_pred().leads_to(lift_state(#[trigger] sub_resource_state_matches(sub_resource, fb)))
    ) by {
        always_tla_forall_apply_for_sub_resource(spec, sub_resource, fb);
        if sub_resource != SubResource::DaemonSet {
            let next_resource = next_resource_after(sub_resource).get_AfterKRequestStep_1();
            lemma_from_after_get_resource_step_to_resource_matches(spec, fb, sub_resource, next_resource);
            leads_to_trans_temp(
                spec, true_pred(), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, fb)),
                lift_state(sub_resource_state_matches(sub_resource, fb))
            );
        } else {
            lemma_from_after_get_daemon_set_step_to_daemon_set_matches(spec, fb);
            leads_to_trans_temp(
                spec, true_pred(), lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::DaemonSet, fb)),
                lift_state(sub_resource_state_matches(SubResource::DaemonSet, fb))
            );
        }
    }

    // Now we further prove stability: given true ~> sub_resource_state_matches(sub_resource, fb)
    // we prove true ~> []sub_resource_state_matches(sub_resource, fb)
    assert forall |sub_resource: SubResource| spec.entails(
        true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, fb))))
    ) by {
        always_tla_forall_apply_for_sub_resource(spec, sub_resource, fb);
        if sub_resource != SubResource::DaemonSet {
            lemma_resource_object_is_stable(spec, sub_resource, fb, true_pred());
        } else {
            lemma_daemon_set_is_stable(spec, fb, true_pred());
        }
    }
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
    ensures
        spec.entails(lift_state(|s: FBCluster| { !s.ongoing_reconciles().contains_key(fb.object_ref()) }).leads_to(lift_state(|s: FBCluster| {
            &&& !s.ongoing_reconciles().contains_key(fb.object_ref())
            &&& s.scheduled_reconciles().contains_key(fb.object_ref())
        }))),
{
    let pre = |s: FBCluster| {
        &&& !s.ongoing_reconciles().contains_key(fb.object_ref())
        &&& !s.scheduled_reconciles().contains_key(fb.object_ref())
    };
    let post = |s: FBCluster| {
        &&& !s.ongoing_reconciles().contains_key(fb.object_ref())
        &&& s.scheduled_reconciles().contains_key(fb.object_ref())
    };
    let input = fb.object_ref();
    FBCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(spec, input, FBCluster::next(), desired_state_is(fb), pre, post);
    valid_implies_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine_temp(spec, lift_state(pre), lift_state(post), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: FBCluster| {!s.ongoing_reconciles().contains_key(fb.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCluster::the_object_in_schedule_has_spec_and_uid_as(fb)))),
    ensures
        spec.entails(lift_state(|s: FBCluster| {
            &&& !s.ongoing_reconciles().contains_key(fb.object_ref())
            &&& s.scheduled_reconciles().contains_key(fb.object_ref())
        }).leads_to(lift_state(no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init)))),
{
    let pre = |s: FBCluster| {
        &&& !s.ongoing_reconciles().contains_key(fb.object_ref())
        &&& s.scheduled_reconciles().contains_key(fb.object_ref())
    };
    let post = no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init);
    let input = (None, Some(fb.object_ref()));
    let stronger_next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
        &&& FBCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()(s)
        &&& FBCluster::the_object_in_schedule_has_spec_and_uid_as(fb)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::crash_disabled()),
        lift_state(FBCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::the_object_in_schedule_has_spec_and_uid_as(fb))
    );
    FBCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, FBCluster::run_scheduled_reconcile(), pre, post);
}

proof fn lemma_from_init_step_to_after_get_service_account_step(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
        spec.entails(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCluster::pending_req_of_key_is_unique_with_unique_id(fb.object_ref())))),
    ensures
        spec.entails(lift_state(no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init)).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb)))),
{
    lemma_from_init_step_to_after_get_secret_step(spec, fb);
    assert_by(spec.entails(lift_state(pending_req_at_after_get_secret_step_with_fb(fb)).leads_to(lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)))), {
        let pre = |req_msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_secret_step(fb, req_msg));
        let post = lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb));
        assert forall |req_msg|
            spec.entails(#[trigger] pre(req_msg).leads_to(post))
        by {
            lemma_from_send_get_secret_req_to_receive_ok_resp_at_after_get_secret_step(spec, fb, req_msg);
        }
        leads_to_exists_intro(spec, pre, post);
        assert_by(tla_exists(pre) == lift_state(pending_req_at_after_get_secret_step_with_fb(fb)), {
            assert forall |ex| #[trigger] lift_state(pending_req_at_after_get_secret_step_with_fb(fb)).satisfied_by(ex)
            implies tla_exists(pre).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[fb.object_ref()].pending_req_msg.get_Some_0();
                assert(pre(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre), lift_state(pending_req_at_after_get_secret_step_with_fb(fb)));
        });
    });
    assert_by(spec.entails(lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb)))), {
        let pre = |resp_msg| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_secret_step(fb, resp_msg));
        let post = lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb));
        assert forall |resp_msg|
            spec.entails(#[trigger] pre(resp_msg).leads_to(post))
        by {
            lemma_from_after_get_secret_step_to_after_get_service_account_step(spec, fb, resp_msg);
        }
        leads_to_exists_intro(spec, pre, post);
        assert_by(tla_exists(pre) == lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)), {
            assert forall |ex| #[trigger] lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)).satisfied_by(ex)
            implies tla_exists(pre).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[fb.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                    &&& resp_msg.content.get_get_response().res.is_Ok()
                };
                assert(pre(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre), lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)));
        });
    });
    leads_to_trans_n!(spec,
        lift_state(no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init)),
        lift_state(pending_req_at_after_get_secret_step_with_fb(fb)),
        lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb))
    );
}

proof fn lemma_from_init_step_to_after_get_secret_step(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
    ensures spec.entails(lift_state(no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init)).leads_to(lift_state(pending_req_at_after_get_secret_step_with_fb(fb)))),
{
    let pre = no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init);
    let post = pending_req_at_after_get_secret_step_with_fb(fb);
    let input = (None, Some(fb.object_ref()));
    let stronger_next = |s, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(FBCluster::next()), lift_state(FBCluster::crash_disabled())
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| FBCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.1.get_Some_0() != fb.object_ref() {
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
    FBCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, FBCluster::continue_reconcile(), pre, post);
}

proof fn lemma_from_send_get_secret_req_to_receive_ok_resp_at_after_get_secret_step(spec: TempPred<FBCluster>, fb: FluentBitView, req_msg: FBMessage)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
    ensures spec.entails(lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_secret_step(fb, req_msg)).leads_to(lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)))),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_get_secret_step(fb, req_msg);
    let post = at_after_get_secret_step_and_exists_ok_resp_in_flight(fb);
    let resource_key = get_secret_req(fb).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
        &&& FBCluster::busy_disabled()(s)
        &&& FBCluster::every_in_flight_msg_has_unique_id()(s)
        &&& desired_state_is(fb)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::crash_disabled()),
        lift_state(FBCluster::busy_disabled()),
        lift_state(FBCluster::every_in_flight_msg_has_unique_id()),
        lift_state(desired_state_is(fb))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| FBCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = FBCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Ok()
                        &&& resp_msg.content.get_get_response().res.get_Ok_0() == s_prime.resources()[resource_key]
                    });
                    assert(post(s_prime));
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && FBCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = FBCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == s_prime.resources()[resource_key]
        });
    }

    FBCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, FBCluster::handle_request(), pre, post);
}

proof fn lemma_from_after_get_secret_step_to_after_get_service_account_step(spec: TempPred<FBCluster>, fb: FluentBitView, resp_msg: FBMessage)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCluster::pending_req_of_key_is_unique_with_unique_id(fb.object_ref())))),
    ensures spec.entails(lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_secret_step(fb, resp_msg)).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb)))),
{
    let pre = resp_msg_is_the_in_flight_ok_resp_at_after_get_secret_step(fb, resp_msg);
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb);
    let input = (Some(resp_msg), Some(fb.object_ref()));
    let stronger_next = |s, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
        &&& FBCluster::busy_disabled()(s)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCluster::pending_req_of_key_is_unique_with_unique_id(fb.object_ref())(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::crash_disabled()),
        lift_state(FBCluster::busy_disabled()),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCluster::pending_req_of_key_is_unique_with_unique_id(fb.object_ref()))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| FBCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.1.get_Some_0() != fb.object_ref() {
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

    FBCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, FBCluster::continue_reconcile(), pre, post);
}

proof fn always_tla_forall_apply_for_sub_resource(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, fb))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, fb))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_daemon_set(res, fb))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(res, fb))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, fb))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, fb))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, fb))))),
    ensures
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fb)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_daemon_set(sub_resource, fb)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fb)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fb)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb)))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, fb)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, fb)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_daemon_set(res, fb)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(res, fb)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, fb)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, fb)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, fb)), sub_resource);
}

}
