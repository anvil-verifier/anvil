// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, dynamic::*};
use crate::kubernetes_cluster::{
    proof::{kubernetes_api_safety, wf1_assistant::controller_action_pre_implies_next_pre},
    spec::{
        controller::common::ControllerAction,
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::controller,
        distributed_system::*,
        message::*,
    },
};
use crate::reconciler::spec::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use builtin::*;
use builtin_macros::*;
use vstd::{option::*, result::*};

verus! {

pub open spec fn partial_spec_with_always_cr_key_exists_and_crash_disabled<K: ResourceView, T>(reconciler: Reconciler<K, T>, cr_key: ObjectRef) -> TempPred<State<T>> {
    sm_partial_spec(reconciler).and(always(lift_state(|s: State<T>| s.resource_key_exists(cr_key)))).and(always(lift_state(crash_disabled::<T>())))
}

pub open spec fn reconciler_init_and_no_pending_req<K: ResourceView, T>(reconciler: Reconciler<K, T>, cr_key: ObjectRef) -> StatePred<State<T>> {
    |s: State<T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state == (reconciler.reconcile_init_state)()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    }
}

pub proof fn lemma_pre_leads_to_post_by_controller<K: ResourceView, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, input: (Option<Message>, Option<ObjectRef>), next: ActionPred<State<T>>, action: ControllerAction<T>, pre: StatePred<State<T>>, post: StatePred<State<T>>)
    requires
        controller(reconciler).actions.contains(action),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && controller_next(reconciler).forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<T>| #[trigger] pre(s) ==> controller_action_pre(reconciler, action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| controller_next(reconciler).weak_fairness(i))),
    ensures
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<T>, (Option<Message>, Option<ObjectRef>)>(spec, |i| controller_next(reconciler).weak_fairness(i), input);

    controller_action_pre_implies_next_pre(reconciler, action, input);
    valid_implies_trans::<State<T>>(lift_state(pre), lift_state(controller_action_pre(reconciler, action, input)), lift_state(controller_next(reconciler).pre(input)));

    controller_next(reconciler).wf1(input, spec, next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_with_assumption_by_controller<K: ResourceView, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, input: (Option<Message>, Option<ObjectRef>), next: ActionPred<State<T>>, action: ControllerAction<T>, assumption: StatePred<State<T>>, pre: StatePred<State<T>>, post: StatePred<State<T>>)
    requires
        controller(reconciler).actions.contains(action),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && assumption(s) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && controller_next(reconciler).forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<T>| #[trigger] pre(s) ==> controller_action_pre(reconciler, action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| controller_next(reconciler).weak_fairness(i))),
    ensures
        spec.entails(lift_state(pre).and(always(lift_state(assumption))).leads_to(lift_state(post))),
{
    use_tla_forall::<State<T>, (Option<Message>, Option<ObjectRef>)>(spec, |i| controller_next(reconciler).weak_fairness(i), input);

    controller_action_pre_implies_next_pre(reconciler, action, input);
    valid_implies_trans::<State<T>>(lift_state(pre), lift_state(controller_action_pre(reconciler, action, input)), lift_state(controller_next(reconciler).pre(input)));

    controller_next(reconciler).wf1_assume(input, spec, next, assumption, pre, post);
}

pub proof fn lemma_reconcile_done_leads_to_reconcile_idle<K: ResourceView, T>(reconciler: Reconciler<K, T>, cr_key: ObjectRef)
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
    let input = (Option::None, Option::Some(cr_key));
    lemma_pre_leads_to_post_by_controller(sm_spec(reconciler), reconciler, input, next(reconciler), end_reconcile(reconciler), pre, post);
}

pub proof fn lemma_reconcile_error_leads_to_reconcile_idle<K: ResourceView, T>(reconciler: Reconciler<K, T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_partial_spec(reconciler).entails(
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
    let input = (Option::None, Option::Some(cr_key));
    lemma_pre_leads_to_post_by_controller(sm_partial_spec(reconciler), reconciler, input, next(reconciler), end_reconcile(reconciler), pre, post);
}

pub proof fn lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init<K: ResourceView, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(always(lift_state(crash_disabled::<T>()))),
        spec.entails(tla_forall(|i| controller_next(reconciler).weak_fairness(i))),
    ensures
        spec.entails(
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
    let stronger_next = |s, s_prime: State<T>| {
        &&& next(reconciler)(s, s_prime)
        &&& !s.crash_enabled
    };
    strengthen_next::<State<T>>(spec, next(reconciler), crash_disabled::<T>(), stronger_next);
    let input = (Option::None, Option::Some(cr_key));
    lemma_pre_leads_to_post_by_controller(spec, reconciler, input, stronger_next, run_scheduled_reconcile(reconciler), pre, post);
}

pub proof fn lemma_true_leads_to_reconcile_scheduled_by_assumption<K: ResourceView, T>(reconciler: Reconciler<K, T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_partial_spec(reconciler).and(always(lift_state(|s: State<T>| s.resource_key_exists(cr_key)))).entails(
            true_pred().leads_to(lift_state(|s: State<T>| s.reconcile_scheduled_for(cr_key)))
        ),
{
    let cr_key_exists = |s: State<T>| s.resource_key_exists(cr_key);
    let spec = sm_partial_spec(reconciler).and(always(lift_state(cr_key_exists)));
    let pre = |s: State<T>| true;
    let post = |s: State<T>| s.reconcile_scheduled_for(cr_key);
    let next_and_cr_exists = |s, s_prime: State<T>| {
        &&& next(reconciler)(s, s_prime)
        &&& cr_key_exists(s)
    };
    strengthen_next::<State<T>>(spec, next(reconciler), cr_key_exists, next_and_cr_exists);
    temp_pred_equality::<State<T>>(lift_state(cr_key_exists), lift_state(schedule_controller_reconcile().pre(cr_key)));
    use_tla_forall::<State<T>, ObjectRef>(spec, |key| schedule_controller_reconcile().weak_fairness(key), cr_key);
    schedule_controller_reconcile().wf1(cr_key, spec, next_and_cr_exists, pre, post);
}

pub proof fn lemma_reconcile_idle_leads_to_reconcile_idle_and_scheduled_by_assumption<K: ResourceView, T>(reconciler: Reconciler<K, T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_partial_spec(reconciler).and(always(lift_state(|s: State<T>| s.resource_key_exists(cr_key)))).entails(
            lift_state(|s: State<T>| !s.reconcile_state_contains(cr_key))
                .leads_to(lift_state(|s: State<T>| {
                    &&& !s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_scheduled_for(cr_key)})
            ),
        )
{
    let spec = sm_partial_spec(reconciler).and(always(lift_state(|s: State<T>| s.resource_key_exists(cr_key))));
    let reconcile_idle = lift_state(|s: State<T>| { !s.reconcile_state_contains(cr_key) });
    let reconcile_scheduled = lift_state(|s: State<T>| { s.reconcile_scheduled_for(cr_key) });
    valid_implies_implies_leads_to(spec, reconcile_idle, true_pred());
    lemma_true_leads_to_reconcile_scheduled_by_assumption(reconciler, cr_key);
    leads_to_trans_temp(spec, reconcile_idle, true_pred(), reconcile_scheduled);
    leads_to_confluence_self_temp::<State<T>>(spec, lift_action(next(reconciler)), reconcile_idle, reconcile_scheduled);
    temp_pred_equality::<State<T>>(reconcile_idle.and(reconcile_scheduled), lift_state(|s: State<T>| {
        &&& !s.reconcile_state_contains(cr_key)
        &&& s.reconcile_scheduled_for(cr_key)}));
}

pub proof fn lemma_cr_always_exists_entails_reconcile_idle_leads_to_reconcile_init_and_no_pending_req<K: ResourceView, T>(reconciler: Reconciler<K, T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        partial_spec_with_always_cr_key_exists_and_crash_disabled(reconciler, cr_key).entails(
            lift_state(|s: State<T>| {!s.reconcile_state_contains(cr_key)})
            .leads_to(lift_state(|s: State<T>| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state == (reconciler.reconcile_init_state)()
                &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
            }))
    ),
{

    lemma_reconcile_idle_leads_to_reconcile_idle_and_scheduled_by_assumption(reconciler, cr_key);
    entails_trans::<State<T>>(partial_spec_with_always_cr_key_exists_and_crash_disabled(reconciler, cr_key), sm_partial_spec(reconciler).and(always(lift_state(|s: State<T>| s.resource_key_exists(cr_key)))), lift_state(|s: State<T>| !s.reconcile_state_contains(cr_key))
    .leads_to(lift_state(|s: State<T>| {
        &&& !s.reconcile_state_contains(cr_key)
        &&& s.reconcile_scheduled_for(cr_key)})
    ));
    lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init(partial_spec_with_always_cr_key_exists_and_crash_disabled(reconciler, cr_key), reconciler, cr_key);

    leads_to_trans_auto::<State<T>>(partial_spec_with_always_cr_key_exists_and_crash_disabled(reconciler, cr_key));
}


pub proof fn lemma_cr_always_exists_entails_reconcile_error_leads_to_reconcile_init_and_no_pending_req<K: ResourceView, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, cr_key: ObjectRef)
    requires
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(sm_partial_spec(reconciler)),
        spec.entails(always(lift_state(|s: State<T>| s.resource_key_exists(cr_key)))),
        spec.entails(always(lift_state(crash_disabled::<T>()))),
    ensures
        spec.entails(
            lift_state(|s: State<T>| {
                &&& s.reconcile_state_contains(cr_key)
                &&& (reconciler.reconcile_error)(s.reconcile_state_of(cr_key).local_state)
            })
                .leads_to(lift_state(reconciler_init_and_no_pending_req(reconciler, cr_key)))
        ),
{
    lemma_reconcile_error_leads_to_reconcile_idle(reconciler, cr_key);
    entails_trans::<State<T>>(partial_spec_with_always_cr_key_exists_and_crash_disabled(reconciler, cr_key), sm_partial_spec(reconciler), lift_state(|s: State<T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& (reconciler.reconcile_error)(s.reconcile_state_of(cr_key).local_state)
        })
        .leads_to(lift_state(|s: State<T>| {
            &&& !s.reconcile_state_contains(cr_key)
        })));
    lemma_reconcile_idle_leads_to_reconcile_idle_and_scheduled_by_assumption(reconciler, cr_key);
    entails_trans::<State<T>>(partial_spec_with_always_cr_key_exists_and_crash_disabled(reconciler, cr_key), sm_partial_spec(reconciler).and(always(lift_state(|s: State<T>| s.resource_key_exists(cr_key)))), lift_state(|s: State<T>| !s.reconcile_state_contains(cr_key))
            .leads_to(lift_state(|s: State<T>| {
                &&& !s.reconcile_state_contains(cr_key)
                &&& s.reconcile_scheduled_for(cr_key)})));
    lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init(partial_spec_with_always_cr_key_exists_and_crash_disabled(reconciler, cr_key), reconciler, cr_key);

    leads_to_trans_auto::<State<T>>(partial_spec_with_always_cr_key_exists_and_crash_disabled(reconciler, cr_key));

    entails_and_n!(spec, sm_partial_spec(reconciler), always(lift_state(|s: State<T>| s.resource_key_exists(cr_key))), always(lift_state(crash_disabled::<T>())));
    entails_trans::<State<T>>(spec, partial_spec_with_always_cr_key_exists_and_crash_disabled(reconciler, cr_key),
    lift_state(|s: State<T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& (reconciler.reconcile_error)(s.reconcile_state_of(cr_key).local_state)
    })
        .leads_to(lift_state(|s: State<T>| {
            &&& s.reconcile_state_contains(cr_key)
            &&& s.reconcile_state_of(cr_key).local_state == (reconciler.reconcile_init_state)()
            &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
        })));
}

}
