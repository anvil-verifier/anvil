// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_cluster::{
    proof::{kubernetes_api_safety, wf1_assistant::controller_action_pre_implies_next_pre},
    spec::{
        controller::common::{ControllerAction, ControllerActionInput},
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::controller,
        distributed_system::*,
        message::*,
        reconciler::Reconciler,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_pre_leads_to_post_by_controller<T>(reconciler: Reconciler<T>, input: ControllerActionInput, next: ActionPred<State<T>>, action: ControllerAction<T>, pre: StatePred<State<T>>, post: StatePred<State<T>>)
    requires
        controller(reconciler).actions.contains(action),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && controller_next(reconciler).forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<T>| #[trigger] pre(s) ==> controller_action_pre(reconciler, action, input)(s),
        sm_spec(reconciler).entails(always(lift_action(next))),
    ensures
        sm_spec(reconciler).entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<T>, ControllerActionInput>(sm_spec(reconciler), |i| controller_next(reconciler).weak_fairness(i), input);

    controller_action_pre_implies_next_pre::<T>(reconciler, action, input);
    valid_implies_trans::<State<T>>(lift_state(pre), lift_state(controller_action_pre(reconciler, action, input)), lift_state(controller_next(reconciler).pre(input)));

    controller_next(reconciler).wf1(input, sm_spec(reconciler), next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_with_assumption_by_controller<T>(reconciler: Reconciler<T>, input: ControllerActionInput, next: ActionPred<State<T>>, action: ControllerAction<T>, assumption: StatePred<State<T>>, pre: StatePred<State<T>>, post: StatePred<State<T>>)
    requires
        controller(reconciler).actions.contains(action),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && assumption(s) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && controller_next(reconciler).forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<T>| #[trigger] pre(s) ==> controller_action_pre(reconciler, action, input)(s),
        sm_spec(reconciler).entails(always(lift_action(next))),
    ensures
        sm_spec(reconciler).entails(lift_state(pre).and(always(lift_state(assumption))).leads_to(lift_state(post))),
{
    use_tla_forall::<State<T>, ControllerActionInput>(sm_spec(reconciler), |i| controller_next(reconciler).weak_fairness(i), input);

    controller_action_pre_implies_next_pre::<T>(reconciler, action, input);
    valid_implies_trans::<State<T>>(lift_state(pre), lift_state(controller_action_pre(reconciler, action, input)), lift_state(controller_next(reconciler).pre(input)));

    controller_next(reconciler).wf1_assume(input, sm_spec(reconciler), next, assumption, pre, post);
}

pub proof fn lemma_reconcile_done_leads_to_reconcile_idle<T>(reconciler: Reconciler<T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<T>| {
                &&& s.reconcile_state_contains(cr_key)
                &&& (reconciler.reconcile_done)(s.reconcile_state_of(cr_key).local_state)
            })
                .leads_to(lift_state(|s: State<T>| {
                    &&& !s.reconcile_state_contains(cr_key)
                }))
        ),
{
    let pre = |s: State<T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& (reconciler.reconcile_done)(s.reconcile_state_of(cr_key).local_state)
    };
    let post = |s: State<T>| {
        &&& !s.reconcile_state_contains(cr_key)
    };
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    lemma_pre_leads_to_post_by_controller::<T>(reconciler, input, next(reconciler), end_reconcile(reconciler), pre, post);
}

pub proof fn lemma_reconcile_error_leads_to_reconcile_idle<T>(reconciler: Reconciler<T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<T>| {
                &&& s.reconcile_state_contains(cr_key)
                &&& (reconciler.reconcile_error)(s.reconcile_state_of(cr_key).local_state)
            })
                .leads_to(lift_state(|s: State<T>| {
                    &&& !s.reconcile_state_contains(cr_key)
                }))
        ),
{
    let pre = |s: State<T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& (reconciler.reconcile_error)(s.reconcile_state_of(cr_key).local_state)
    };
    let post = |s: State<T>| {
        &&& !s.reconcile_state_contains(cr_key)
    };
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    lemma_pre_leads_to_post_by_controller::<T>(reconciler, input, next(reconciler), end_reconcile(reconciler), pre, post);
}

pub proof fn lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init<T>(reconciler: Reconciler<T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<T>| {
                &&& !s.reconcile_state_contains(cr_key)
                &&& s.reconcile_scheduled_for(cr_key)
            })
                .leads_to(lift_state(|s: State<T>| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state == (reconciler.reconcile_init_state)()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
                }))
        ),
{
    let pre = |s: State<T>| {
        &&& !s.reconcile_state_contains(cr_key)
        &&& s.reconcile_scheduled_for(cr_key)
    };
    let post = |s: State<T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state == (reconciler.reconcile_init_state)()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    lemma_pre_leads_to_post_by_controller::<T>(reconciler, input, next(reconciler), run_scheduled_reconcile(reconciler), pre, post);
}

// TODO: we need a lemma that says with the assumption that cr always exists, true ~> reconcile_scheduled_for_cr

}
