// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, resource::*};
use crate::kubernetes_cluster::{
    proof::{
        controller_runtime::*, kubernetes_api_safety,
        wf1_assistant::controller_action_pre_implies_next_pre,
    },
    spec::{
        cluster::*,
        controller::common::ControllerAction,
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::controller,
        message::*,
    },
};
use crate::reconciler::spec::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

pub open spec fn partial_spec_with_always_cr_key_exists_and_crash_disabled
<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(cr_key: ObjectRef) -> TempPred<State<K, T>> {
    sm_partial_spec::<K, T, ReconcilerType>()
    .and(always(lift_state(|s: State<K, T>| {
        &&& s.resource_key_exists(cr_key)
        &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
    })))
    .and(always(lift_state(crash_disabled::<K, T>())))
}

pub proof fn lemma_pre_leads_to_post_by_controller<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, input: (Option<Message>, Option<ObjectRef>), next: ActionPred<State<K, T>>,
    action: ControllerAction<K, T>, pre: StatePred<State<K, T>>, post: StatePred<State<K, T>>
)
    requires
        controller::<K, T, ReconcilerType>().actions.contains(action),
        forall |s, s_prime: State<K, T>| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<K, T>| pre(s) && #[trigger] next(s, s_prime) && controller_next::<K, T, ReconcilerType>().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<K, T>| #[trigger] pre(s) ==> controller_action_pre::<K, T, ReconcilerType>(action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| controller_next::<K, T, ReconcilerType>().weak_fairness(i))),
    ensures
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<K, T>, (Option<Message>, Option<ObjectRef>)>(
        spec, |i| controller_next::<K, T, ReconcilerType>().weak_fairness(i), input
    );

    controller_action_pre_implies_next_pre::<K, T, ReconcilerType>(action, input);
    valid_implies_trans::<State<K, T>>(
        lift_state(pre),
        lift_state(controller_action_pre::<K, T, ReconcilerType>(action, input)),
        lift_state(controller_next::<K, T, ReconcilerType>().pre(input))
    );

    controller_next::<K, T, ReconcilerType>().wf1(input, spec, next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_by_schedule_controller_reconcile<K: ResourceView, T>(
    spec: TempPred<State<K, T>>, input: ObjectRef, next: ActionPred<State<K, T>>,
    pre: StatePred<State<K, T>>, post: StatePred<State<K, T>>
)
    requires
        forall |s, s_prime: State<K, T>| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<K, T>| pre(s) && #[trigger] next(s, s_prime) && schedule_controller_reconcile::<K, T>().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<K, T>| #[trigger] pre(s) ==> schedule_controller_reconcile::<K, T>().pre(input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| schedule_controller_reconcile::<K, T>().weak_fairness(i))),
    ensures
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<K, T>, ObjectRef>(
        spec, |i| schedule_controller_reconcile::<K, T>().weak_fairness(i), input
    );
    schedule_controller_reconcile::<K, T>().wf1(input, spec, next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec<K: ResourceView, T>(
    spec: TempPred<State<K, T>>, input: ObjectRef, next: ActionPred<State<K, T>>,
    c: StatePred<State<K, T>>, pre: StatePred<State<K, T>>, post: StatePred<State<K, T>>
)
    requires
        forall |s, s_prime: State<K, T>| pre(s) && c(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<K, T>| pre(s) && c(s) && #[trigger] next(s, s_prime) && schedule_controller_reconcile::<K, T>().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<K, T>| #[trigger] pre(s) && c(s) ==> schedule_controller_reconcile::<K, T>().pre(input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| schedule_controller_reconcile::<K, T>().weak_fairness(i))),
        spec.entails(always(lift_state(c))),
    ensures
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<K, T>, ObjectRef>(
        spec, |i| schedule_controller_reconcile::<K, T>().weak_fairness(i), input
    );
    schedule_controller_reconcile::<K, T>().wf1_borrow_from_spec(input, spec, next, c, pre, post);
}

pub proof fn lemma_reconcile_done_leads_to_reconcile_idle
<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(spec: TempPred<State<K, T>>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| controller_next::<K, T, ReconcilerType>().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(reconciler_reconcile_done::<K, T, ReconcilerType>(cr_key))
                .leads_to(lift_state(|s: State<K, T>| {
                    &&& !s.reconcile_state_contains(cr_key)
                }))
        ),
{
    let pre = reconciler_reconcile_done::<K, T, ReconcilerType>(cr_key);
    let post = |s: State<K, T>| {
        &&& !s.reconcile_state_contains(cr_key)
    };
    let input = (Option::None, Option::Some(cr_key));
    lemma_pre_leads_to_post_by_controller::<K, T, ReconcilerType>(
        spec, input, next::<K, T, ReconcilerType>(),
        end_reconcile::<K, T, ReconcilerType>(), pre, post
    );
}

pub proof fn lemma_reconcile_error_leads_to_reconcile_idle
<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(spec: TempPred<State<K, T>>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| controller_next::<K, T, ReconcilerType>().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(reconciler_reconcile_error::<K, T, ReconcilerType>(cr_key))
                .leads_to(lift_state(|s: State<K, T>| {
                    &&& !s.reconcile_state_contains(cr_key)
                }))
        ),
{
    let pre = reconciler_reconcile_error::<K, T, ReconcilerType>(cr_key);
    let post = |s: State<K, T>| { !s.reconcile_state_contains(cr_key) };
    let input = (Option::None, Option::Some(cr_key));
    lemma_pre_leads_to_post_by_controller::<K, T, ReconcilerType>(
        spec, input,
        next::<K, T, ReconcilerType>(), end_reconcile::<K, T, ReconcilerType>(), pre, post
    );
}

pub proof fn lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init
<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(spec: TempPred<State<K, T>>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(always(lift_state(crash_disabled::<K, T>()))),
        spec.entails(tla_forall(|i| controller_next::<K, T, ReconcilerType>().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<K, T>| {
                &&& !s.reconcile_state_contains(cr_key)
                &&& s.reconcile_scheduled_for(cr_key)
            })
                .leads_to(lift_state(|s: State<K, T>| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state == ReconcilerType::reconcile_init_state()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
                }))
        ),
{
    let pre = |s: State<K, T>| {
        &&& !s.reconcile_state_contains(cr_key)
        &&& s.reconcile_scheduled_for(cr_key)
    };
    let post = |s: State<K, T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state == ReconcilerType::reconcile_init_state()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    let stronger_next = |s, s_prime: State<K, T>| {
        &&& next::<K, T, ReconcilerType>()(s, s_prime)
        &&& !s.crash_enabled
    };
    strengthen_next::<State<K, T>>(spec, next::<K, T, ReconcilerType>(), crash_disabled::<K, T>(), stronger_next);
    let input = (Option::None, Option::Some(cr_key));
    lemma_pre_leads_to_post_by_controller::<K, T, ReconcilerType>(
        spec, input, stronger_next, run_scheduled_reconcile::<K, T, ReconcilerType>(), pre, post
    );
}

pub proof fn lemma_true_leads_to_reconcile_scheduled_by_assumption<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, cr_key: ObjectRef
)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_state(|s: State<K, T>| {
            &&& s.resource_key_exists(cr_key)
            &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
        }))),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|input| schedule_controller_reconcile().weak_fairness(input))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: State<K, T>| s.reconcile_scheduled_for(cr_key)))
        ),
{
    let cr_key_exists = |s: State<K, T>| {
        &&& s.resource_key_exists(cr_key)
        &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
    };
    let pre = |s: State<K, T>| true;
    let post = |s: State<K, T>| s.reconcile_scheduled_for(cr_key);
    let next_and_cr_exists = |s, s_prime: State<K, T>| {
        &&& next::<K, T, ReconcilerType>()(s, s_prime)
        &&& cr_key_exists(s)
    };
    strengthen_next::<State<K, T>>(spec, next::<K, T, ReconcilerType>(), cr_key_exists, next_and_cr_exists);
    temp_pred_equality::<State<K, T>>(lift_state(cr_key_exists), lift_state(schedule_controller_reconcile().pre(cr_key)));
    use_tla_forall::<State<K, T>, ObjectRef>(spec, |key| schedule_controller_reconcile().weak_fairness(key), cr_key);

    entails_and_temp(spec, always(lift_state(|s: State<K, T>| {
        &&& s.resource_key_exists(cr_key)
        &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
    })), always(lift_state(|s: State<K, T>| { cr_key.kind.is_CustomResourceKind() })));
    always_and_equality(lift_state(|s: State<K, T>| {
        &&& s.resource_key_exists(cr_key)
        &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
    }), lift_state(|s: State<K, T>| { cr_key.kind.is_CustomResourceKind() }));
    temp_pred_equality(lift_state(|s: State<K, T>| {
        &&& s.resource_key_exists(cr_key)
        &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
    }).and(lift_state(|s: State<K, T>| { cr_key.kind.is_CustomResourceKind() })), lift_state(pre).implies(lift_state(schedule_controller_reconcile::<K, T>().pre(cr_key))));

    schedule_controller_reconcile::<K, T>().wf1(cr_key, spec, next_and_cr_exists, pre, post);
}

pub proof fn lemma_reconcile_idle_leads_to_reconcile_idle_and_scheduled_by_assumption
<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(spec: TempPred<State<K, T>>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_state(|s: State<K, T>| {
            &&& s.resource_key_exists(cr_key)
            &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
        }))),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|input| schedule_controller_reconcile().weak_fairness(input))),
    ensures
        spec.entails(
            lift_state(|s: State<K, T>| !s.reconcile_state_contains(cr_key))
                .leads_to(lift_state(|s: State<K, T>| {
                    &&& !s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_scheduled_for(cr_key)})
            ),
        )
{
    let reconcile_idle = lift_state(|s: State<K, T>| { !s.reconcile_state_contains(cr_key) });
    let reconcile_scheduled = lift_state(|s: State<K, T>| { s.reconcile_scheduled_for(cr_key) });
    valid_implies_implies_leads_to(spec, reconcile_idle, true_pred());
    lemma_true_leads_to_reconcile_scheduled_by_assumption::<K, T, ReconcilerType>(spec, cr_key);
    leads_to_trans_temp(spec, reconcile_idle, true_pred(), reconcile_scheduled);
    leads_to_confluence_self_temp::<State<K, T>>(
        spec, lift_action(next::<K, T, ReconcilerType>()), reconcile_idle, reconcile_scheduled
    );
    temp_pred_equality::<State<K, T>>(
        reconcile_idle.and(reconcile_scheduled),
        lift_state(|s: State<K, T>| {
            &&& !s.reconcile_state_contains(cr_key)
            &&& s.reconcile_scheduled_for(cr_key)
        })
    );
}

pub proof fn lemma_cr_always_exists_entails_reconcile_idle_leads_to_reconcile_init_and_no_pending_req
<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(spec: TempPred<State<K, T>>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_state(|s: State<K, T>| {
            &&& s.resource_key_exists(cr_key)
            &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
        }))),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| controller_next::<K, T, ReconcilerType>().weak_fairness(i))),
        spec.entails(tla_forall(|input| schedule_controller_reconcile().weak_fairness(input))),
        spec.entails(always(lift_state(crash_disabled::<K, T>()))),
    ensures
        spec.entails(
            lift_state(|s: State<K, T>| !s.reconcile_state_contains(cr_key))
            .leads_to(lift_state(|s: State<K, T>| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state == ReconcilerType::reconcile_init_state()
                &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
            }))
    ),
{
    lemma_reconcile_idle_leads_to_reconcile_idle_and_scheduled_by_assumption::<K, T, ReconcilerType>(spec, cr_key);
    lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init::<K, T, ReconcilerType>(spec, cr_key);

    leads_to_trans_n!(
        spec,
        lift_state(|s: State<K, T>| !s.reconcile_state_contains(cr_key)),
        lift_state(|s: State<K, T>| {
            &&& !s.reconcile_state_contains(cr_key)
            &&& s.reconcile_scheduled_for(cr_key)}),
        lift_state(|s: State<K, T>| {
            &&& s.reconcile_state_contains(cr_key)
            &&& s.reconcile_state_of(cr_key).local_state == ReconcilerType::reconcile_init_state()
            &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
        })
    );
}


pub proof fn lemma_cr_always_exists_entails_reconcile_error_leads_to_reconcile_init_and_no_pending_req
<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(spec: TempPred<State<K, T>>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_state(|s: State<K, T>| {
            &&& s.resource_key_exists(cr_key)
            &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
        }))),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| controller_next::<K, T, ReconcilerType>().weak_fairness(i))),
        spec.entails(tla_forall(|input| schedule_controller_reconcile().weak_fairness(input))),
        spec.entails(always(lift_state(crash_disabled::<K, T>()))),
    ensures
        spec.entails(
            lift_state(reconciler_reconcile_error::<K, T, ReconcilerType>(cr_key))
                .leads_to(lift_state(reconciler_init_and_no_pending_req::<K, T, ReconcilerType>(cr_key)))
        ),
{
    lemma_reconcile_error_leads_to_reconcile_idle::<K, T, ReconcilerType>(spec, cr_key);
    lemma_reconcile_idle_leads_to_reconcile_idle_and_scheduled_by_assumption::<K, T, ReconcilerType>(spec, cr_key);
    lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init::<K, T, ReconcilerType>(spec, cr_key);
    leads_to_trans_auto::<State<K, T>>(spec);
}

}
