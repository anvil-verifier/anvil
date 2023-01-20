// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::kubernetes_cluster::{
    proof::common::{kubernetes_api_safety, wf1_assistant::controller_action_pre_implies_next_pre},
    spec::{
        common::*,
        controller::common::{ControllerAction, ControllerActionInput},
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile, trigger_reconcile,
        },
        controller::state_machine::controller,
        distributed_system::*,
        reconciler::Reconciler,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_pre_leads_to_post_by_controller(reconciler: Reconciler, input: ControllerActionInput, action: ControllerAction, pre: StatePred<State>, post: StatePred<State>)
    requires
        controller(reconciler).actions.contains(action),
        forall |s, s_prime: State| pre(s) && #[trigger] next(reconciler)(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State| pre(s) && #[trigger] next(reconciler)(s, s_prime) && controller_next(reconciler).forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State| #[trigger] pre(s) ==> controller_action_pre(reconciler, action, input)(s),
    ensures
        sm_spec(reconciler).entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State, ControllerActionInput>(sm_spec(reconciler), |i| controller_next(reconciler).weak_fairness(i), input);

    controller_action_pre_implies_next_pre(reconciler, action, input);
    valid_implies_trans::<State>(lift_state(pre), lift_state(controller_action_pre(reconciler, action, input)), lift_state(controller_next(reconciler).pre(input)));

    controller_next(reconciler).wf1(input, sm_spec(reconciler), next(reconciler), pre, post);
}

pub proof fn lemma_pre_leads_to_post_with_assumption_by_controller(reconciler: Reconciler, input: ControllerActionInput, action: ControllerAction, assumption: StatePred<State>, pre: StatePred<State>, post: StatePred<State>)
    requires
        controller(reconciler).actions.contains(action),
        forall |s, s_prime: State| pre(s) && #[trigger] next(reconciler)(s, s_prime) && assumption(s) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State| pre(s) && #[trigger] next(reconciler)(s, s_prime) && controller_next(reconciler).forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State| #[trigger] pre(s) ==> controller_action_pre(reconciler, action, input)(s),
    ensures
        sm_spec(reconciler).entails(lift_state(pre).and(always(lift_state(assumption))).leads_to(lift_state(post))),
{
    use_tla_forall::<State, ControllerActionInput>(sm_spec(reconciler), |i| controller_next(reconciler).weak_fairness(i), input);

    controller_action_pre_implies_next_pre(reconciler, action, input);
    valid_implies_trans::<State>(lift_state(pre), lift_state(controller_action_pre(reconciler, action, input)), lift_state(controller_next(reconciler).pre(input)));

    controller_next(reconciler).wf1_assume(input, sm_spec(reconciler), next(reconciler), assumption, pre, post);
}

pub proof fn lemma_relevant_event_sent_leads_to_reconcile_triggered(reconciler: Reconciler, msg: Message, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::CustomController
                &&& msg.content.is_WatchEvent()
                &&& (reconciler.reconcile_trigger)(msg) === Option::Some(cr_key)
                &&& !s.reconcile_state_contains(cr_key)
            })
                .leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state === (reconciler.reconcile_init_state)()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
                }))
        ),
{
    let pre = |s: State| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::CustomController
        &&& msg.content.is_WatchEvent()
        &&& (reconciler.reconcile_trigger)(msg) === Option::Some(cr_key)
        &&& !s.reconcile_state_contains(cr_key)
    };
    let post = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state === (reconciler.reconcile_init_state)()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    let input = ControllerActionInput {
        recv: Option::Some(msg),
        scheduled_cr_key: Option::None,
    };
    lemma_pre_leads_to_post_by_controller(reconciler, input, trigger_reconcile(reconciler), pre, post);
}

pub proof fn lemma_reconcile_done_leads_to_reconcile_scheduled(reconciler: Reconciler, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& (reconciler.reconcile_done)(s.reconcile_state_of(cr_key).local_state)
            })
                .leads_to(lift_state(|s: State| {
                    &&& !s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_scheduled_for(cr_key)
                }))
        ),
{
    let pre = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& (reconciler.reconcile_done)(s.reconcile_state_of(cr_key).local_state)
    };
    let post = |s: State| {
        &&& !s.reconcile_state_contains(cr_key)
        &&& s.reconcile_scheduled_for(cr_key)
    };
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    lemma_pre_leads_to_post_by_controller(reconciler, input, end_reconcile(reconciler), pre, post);
}

pub proof fn lemma_scheduled_reconcile_leads_to_init(reconciler: Reconciler, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State| {
                &&& !s.reconcile_state_contains(cr_key)
                &&& s.reconcile_scheduled_for(cr_key)
            })
                .leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state === (reconciler.reconcile_init_state)()
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
        &&& s.reconcile_state_of(cr_key).local_state === (reconciler.reconcile_init_state)()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    lemma_pre_leads_to_post_by_controller(reconciler, input, run_scheduled_reconcile(reconciler), pre, post);
}

pub proof fn lemma_reconcile_done_leads_to_reconcile_triggered(reconciler: Reconciler, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& (reconciler.reconcile_done)(s.reconcile_state_of(cr_key).local_state)
            })
                .leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state === (reconciler.reconcile_init_state)()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
                }))
        ),
{
    lemma_reconcile_done_leads_to_reconcile_scheduled(reconciler, cr_key);
    lemma_scheduled_reconcile_leads_to_init(reconciler, cr_key);
    let reconcile_ended = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& (reconciler.reconcile_done)(s.reconcile_state_of(cr_key).local_state)
    };
    let reconcile_rescheduled = |s: State| {
        &&& !s.reconcile_state_contains(cr_key)
        &&& s.reconcile_scheduled_for(cr_key)
    };
    let reconcile_at_init = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state === (reconciler.reconcile_init_state)()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    leads_to_trans::<State>(sm_spec(reconciler), reconcile_ended, reconcile_rescheduled, reconcile_at_init);
}

}
