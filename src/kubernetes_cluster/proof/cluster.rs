// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    client,
    client::{client, ClientActionInput, ClientState},
    controller::common::{
        ControllerAction, ControllerActionInput, ControllerState, OngoingReconcile,
    },
    controller::state_machine::controller,
    distributed_system::*,
    kubernetes_api::common::{KubernetesAPIAction, KubernetesAPIActionInput, KubernetesAPIState},
    kubernetes_api::state_machine::kubernetes_api,
    message::*,
    network,
    network::{multiset_contains_msg, network, NetworkState},
};
use crate::reconciler::spec::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use builtin::*;
use builtin_macros::*;
use vstd::{map::*, option::*, seq::*, set::*};

verus! {

/// Prove weak_fairness is stable.
proof fn valid_stable_action_weak_fairness<K: ResourceView, T, Output>(action: Action<State<K, T>, (), Output>)
    ensures
        valid(stable(action.weak_fairness(()))),
{
    let split_always = always(lift_state(action.pre(()))).implies(eventually(lift_action(action.forward(()))));
    always_p_stable::<State<K, T>>(split_always);
}

/// Prove weak_fairness for all input is stable.
proof fn valid_stable_tla_forall_action_weak_fairness<K: ResourceView, T, Input, Output>(
    action: Action<State<K, T>, Input, Output>
)
    ensures
        valid(stable(tla_forall(|input| action.weak_fairness(input)))),
{
    let split_always = |input| always(lift_state(action.pre(input))).implies(eventually(lift_action(action.forward(input))));
    tla_forall_always_equality_variant::<State<K, T>, Input>(|input| action.weak_fairness(input), split_always);
    always_p_stable::<State<K, T>>(tla_forall(split_always));
}

/// Prove partial_spec is stable.
pub proof fn valid_stable_sm_partial_spec<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(reconciler: ReconcilerType)
    ensures
        valid(stable(sm_partial_spec(reconciler))),
{
    always_p_stable::<State<K, T>>(lift_action(next(reconciler)));
    valid_stable_tla_forall_action_weak_fairness::<K, T, Option<Message>, ()>(kubernetes_api_next());
    valid_stable_tla_forall_action_weak_fairness::<K, T, (Option<Message>, Option<ObjectRef>), ()>(controller_next(reconciler));
    valid_stable_tla_forall_action_weak_fairness::<K, T, ObjectRef, ()>(schedule_controller_reconcile());
    valid_stable_action_weak_fairness::<K, T, ()>(disable_crash());

    stable_and_n!(
        always(lift_action(next(reconciler))),
        tla_forall(|input| kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| controller_next(reconciler).weak_fairness(input)),
        tla_forall(|input| schedule_controller_reconcile().weak_fairness(input)),
        disable_crash().weak_fairness(())
    );
}

pub proof fn lemma_true_leads_to_crash_always_disabled<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, reconciler: ReconcilerType
)
    requires
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(disable_crash().weak_fairness(())),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(crash_disabled::<K, T>())))),
{
    let true_state = |s: State<K, T>| true;
    disable_crash().wf1((), spec, next(reconciler), true_state, crash_disabled::<K, T>());
    leads_to_stable_temp::<State<K, T>>(spec, lift_action(next(reconciler)), true_pred(), lift_state(crash_disabled::<K, T>()));
}

pub proof fn lemma_any_pred_leads_to_crash_always_disabled<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, reconciler: ReconcilerType, any_pred: TempPred<State<K, T>>
)
    requires
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(disable_crash().weak_fairness(())),
    ensures
        spec.entails(any_pred.leads_to(always(lift_state(crash_disabled::<K, T>())))),
{
    valid_implies_implies_leads_to::<State<K, T>>(spec, any_pred, true_pred());
    lemma_true_leads_to_crash_always_disabled::<K, T, ReconcilerType>(spec, reconciler);
    leads_to_trans_temp::<State<K, T>>(spec, any_pred, true_pred(), always(lift_state(crash_disabled::<K, T>())));
}

}
