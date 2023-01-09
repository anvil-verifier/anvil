// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::kubernetes_cluster::{
    proof::{kubernetes_api_safety, wf1_assistant::controller_action_pre_implies_next_pre},
    spec::{
        common::*,
        controller,
        controller::{ending_step, relevant_cr_key, ControllerAction, ControllerActionInput},
        distributed_system::*,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_pre_leads_to_post_by_controller(input: ControllerActionInput, action: ControllerAction, pre: StatePred<State>, post: StatePred<State>)
    requires
        controller::controller().actions.contains(action),
        forall |s, s_prime: State| pre(s) && #[trigger] next()(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State| pre(s) && #[trigger] next()(s, s_prime) && controller_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State| #[trigger] pre(s) ==> controller_action_pre(action, input)(s),
    ensures
        sm_spec().entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State, ControllerActionInput>(sm_spec(), |i| controller_next().weak_fairness(i), input);

    controller_action_pre_implies_next_pre(action, input);
    valid_implies_trans::<State>(lift_state(pre), lift_state(controller_action_pre(action, input)), lift_state(controller_next().pre(input)));

    controller_next().wf1(input, sm_spec(), next(), pre, post);
}

pub proof fn lemma_pre_leads_to_post_with_asm_by_controller(input: ControllerActionInput, action: ControllerAction, asm: StatePred<State>, pre: StatePred<State>, post: StatePred<State>)
    requires
        controller::controller().actions.contains(action),
        forall |s, s_prime: State| pre(s) && #[trigger] next()(s, s_prime) && asm(s) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State| pre(s) && #[trigger] next()(s, s_prime) && controller_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State| #[trigger] pre(s) ==> controller_action_pre(action, input)(s),
    ensures
        sm_spec().entails(lift_state(pre).and(always(lift_state(asm))).leads_to(lift_state(post))),
{
    use_tla_forall::<State, ControllerActionInput>(sm_spec(), |i| controller_next().weak_fairness(i), input);

    controller_action_pre_implies_next_pre(action, input);
    valid_implies_trans::<State>(lift_state(pre), lift_state(controller_action_pre(action, input)), lift_state(controller_next().pre(input)));

    controller_next().wf1_assume(input, sm_spec(), next(), asm, pre, post);
}

pub proof fn lemma_relevant_event_sent_leads_to_reconcile_triggered(msg: Message, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::CustomController
                &&& msg.content.is_WatchEvent()
                &&& relevant_cr_key(msg) === Option::Some(cr_key)
                &&& !s.reconcile_state_contains(cr_key)
            })
                .leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::Init
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
                }))
        ),
{
    let pre = |s: State| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::CustomController
        &&& msg.content.is_WatchEvent()
        &&& relevant_cr_key(msg) === Option::Some(cr_key)
        &&& !s.reconcile_state_contains(cr_key)
    };
    let post = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::Init
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    let input = ControllerActionInput {
        recv: Option::Some(msg),
        scheduled_cr_key: Option::None,
    };
    lemma_pre_leads_to_post_by_controller(input, controller::trigger_reconcile(), pre, post);
}

pub proof fn lemma_reconcile_ended_leads_to_reconcile_ended(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
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
    lemma_pre_leads_to_post_by_controller(input, controller::end_reconcile(), pre, post);
}

pub proof fn lemma_scheduled_reconcile_leads_to_init(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& !s.reconcile_state_contains(cr_key)
                &&& s.reconcile_scheduled_for(cr_key)
            })
                .leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::Init
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
        &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::Init
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    lemma_pre_leads_to_post_by_controller(input, controller::run_scheduled_reconcile(), pre, post);
}

pub proof fn lemma_reconcile_ended_leads_to_init(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& ending_step(s.reconcile_state_of(cr_key).reconcile_step)
            })
                .leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::Init
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
        &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::Init
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    leads_to_trans::<State>(sm_spec(), reconcile_ended, reconcile_rescheduled, reconcile_at_init);
}

}
