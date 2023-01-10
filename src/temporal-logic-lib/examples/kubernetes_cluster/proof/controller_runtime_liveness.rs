// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::kubernetes_cluster::{
    proof::{kubernetes_api_safety, wf1_assistant::controller_action_pre_implies_next_pre},
    spec::{
        common::*,
        controller::common::{
            ending_step, ControllerAction, ControllerActionInput, ReconcileCoreStep, Reconciler,
        },
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile, trigger_reconcile,
        },
        controller::state_machine::controller,
        distributed_system::*,
        reconcilers::simple_reconciler::simple_reconciler,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_pre_leads_to_post_by_controller(r: Reconciler, input: ControllerActionInput, action: ControllerAction, pre: StatePred<State>, post: StatePred<State>)
    requires
        controller(r).actions.contains(action),
        forall |s, s_prime: State| pre(s) && #[trigger] next(r)(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State| pre(s) && #[trigger] next(r)(s, s_prime) && controller_next(r).forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State| #[trigger] pre(s) ==> controller_action_pre(r, action, input)(s),
    ensures
        sm_spec(r).entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State, ControllerActionInput>(sm_spec(r), |i| controller_next(r).weak_fairness(i), input);

    controller_action_pre_implies_next_pre(r, action, input);
    valid_implies_trans::<State>(lift_state(pre), lift_state(controller_action_pre(r, action, input)), lift_state(controller_next(r).pre(input)));

    controller_next(r).wf1(input, sm_spec(r), next(r), pre, post);
}

pub proof fn lemma_pre_leads_to_post_with_asm_by_controller(r: Reconciler, input: ControllerActionInput, action: ControllerAction, asm: StatePred<State>, pre: StatePred<State>, post: StatePred<State>)
    requires
        controller(r).actions.contains(action),
        forall |s, s_prime: State| pre(s) && #[trigger] next(r)(s, s_prime) && asm(s) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State| pre(s) && #[trigger] next(r)(s, s_prime) && controller_next(r).forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State| #[trigger] pre(s) ==> controller_action_pre(r, action, input)(s),
    ensures
        sm_spec(r).entails(lift_state(pre).and(always(lift_state(asm))).leads_to(lift_state(post))),
{
    use_tla_forall::<State, ControllerActionInput>(sm_spec(r), |i| controller_next(r).weak_fairness(i), input);

    controller_action_pre_implies_next_pre(r, action, input);
    valid_implies_trans::<State>(lift_state(pre), lift_state(controller_action_pre(r, action, input)), lift_state(controller_next(r).pre(input)));

    controller_next(r).wf1_assume(input, sm_spec(r), next(r), asm, pre, post);
}

pub proof fn lemma_reconcile_ended_leads_to_reconcile_ended(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& ending_step(s.reconcile_state_of(cr_key).reconcile_step)
            })
                .leads_to(lift_state(|s: State| {
                    &&& !s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_scheduled_for(cr_key)
                }))
        ),
{
    let pre = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& ending_step(s.reconcile_state_of(cr_key).reconcile_step)
    };
    let post = |s: State| {
        &&& !s.reconcile_state_contains(cr_key)
        &&& s.reconcile_scheduled_for(cr_key)
    };
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    lemma_pre_leads_to_post_by_controller(simple_reconciler(), input, end_reconcile(), pre, post);
}

pub proof fn lemma_scheduled_reconcile_leads_to_init(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| {
                &&& !s.reconcile_state_contains(cr_key)
                &&& s.reconcile_scheduled_for(cr_key)
            })
                .leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
                }))
        ),
{
    let pre = |s: State| {
        &&& !s.reconcile_state_contains(cr_key)
        &&& s.reconcile_scheduled_for(cr_key)
    };
    let post = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    lemma_pre_leads_to_post_by_controller(simple_reconciler(), input, run_scheduled_reconcile(), pre, post);
}

pub proof fn lemma_reconcile_ended_leads_to_init(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& ending_step(s.reconcile_state_of(cr_key).reconcile_step)
            })
                .leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
                }))
        ),
{
    lemma_reconcile_ended_leads_to_reconcile_ended(cr_key);
    lemma_scheduled_reconcile_leads_to_init(cr_key);
    let reconcile_ended = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& ending_step(s.reconcile_state_of(cr_key).reconcile_step)
    };
    let reconcile_rescheduled = |s: State| {
        &&& !s.reconcile_state_contains(cr_key)
        &&& s.reconcile_scheduled_for(cr_key)
    };
    let reconcile_at_init = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === ReconcileCoreStep::Init
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    leads_to_trans::<State>(sm_spec(simple_reconciler()), reconcile_ended, reconcile_rescheduled, reconcile_at_init);
}

}
