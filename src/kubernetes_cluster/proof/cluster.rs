// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    client,
    client::{client, ClientActionInput, ClientState},
    cluster::*,
    controller::common::{
        ControllerAction, ControllerActionInput, ControllerState, OngoingReconcile,
    },
    controller::state_machine::controller,
    kubernetes_api::common::{KubernetesAPIAction, KubernetesAPIActionInput, KubernetesAPIState},
    kubernetes_api::state_machine::kubernetes_api,
    message::*,
    network,
    network::{network, NetworkState},
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

/// Prove weak_fairness is stable.
pub proof fn action_weak_fairness_is_stable<K: ResourceView, T, Output>(action: Action<State<K, T>, (), Output>)
    ensures
        valid(stable(action.weak_fairness(()))),
{
    let split_always = always(lift_state(action.pre(()))).implies(eventually(lift_action(action.forward(()))));
    always_p_is_stable::<State<K, T>>(split_always);
}

/// Prove weak_fairness for all input is stable.
pub proof fn tla_forall_action_weak_fairness_is_stable<K: ResourceView, T, Input, Output>(
    action: Action<State<K, T>, Input, Output>
)
    ensures
        valid(stable(tla_forall(|input| action.weak_fairness(input)))),
{
    let split_always = |input| always(lift_state(action.pre(input))).implies(eventually(lift_action(action.forward(input))));
    tla_forall_always_equality_variant::<State<K, T>, Input>(|input| action.weak_fairness(input), split_always);
    always_p_is_stable::<State<K, T>>(tla_forall(split_always));
}

/// Prove partial_spec is stable.
pub proof fn sm_partial_spec_is_stable<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>()
    ensures
        valid(stable(sm_partial_spec::<K, T, ReconcilerType>())),
{
    always_p_is_stable::<State<K, T>>(lift_action(next::<K, T, ReconcilerType>()));
    tla_forall_action_weak_fairness_is_stable::<K, T, Option<Message>, ()>(kubernetes_api_next());
    tla_forall_action_weak_fairness_is_stable::<K, T, (Option<Message>, Option<ObjectRef>), ()>(controller_next::<K, T, ReconcilerType>());
    tla_forall_action_weak_fairness_is_stable::<K, T, ObjectRef, ()>(schedule_controller_reconcile());
    action_weak_fairness_is_stable::<K, T, ()>(disable_crash());
    action_weak_fairness_is_stable::<K, T, ()>(disable_busy());

    stable_and_n!(
        always(lift_action(next::<K, T, ReconcilerType>())),
        tla_forall(|input| kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| controller_next::<K, T, ReconcilerType>().weak_fairness(input)),
        tla_forall(|input| schedule_controller_reconcile().weak_fairness(input)),
        disable_crash().weak_fairness(()),
        disable_busy().weak_fairness(())
    );
}

pub proof fn lemma_true_leads_to_crash_always_disabled<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>,
)
    requires
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(disable_crash().weak_fairness(())),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(crash_disabled::<K, T>())))),
{
    let true_state = |s: State<K, T>| true;
    disable_crash().wf1((), spec, next::<K, T, ReconcilerType>(), true_state, crash_disabled::<K, T>());
    leads_to_stable_temp::<State<K, T>>(spec, lift_action(next::<K, T, ReconcilerType>()), true_pred(), lift_state(crash_disabled::<K, T>()));
}

pub proof fn lemma_true_leads_to_busy_always_disabled<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>,
)
    requires
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(disable_busy().weak_fairness(())),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(busy_disabled::<K, T>())))),
{
    let true_state = |s: State<K, T>| true;
    disable_busy().wf1((), spec, next::<K, T, ReconcilerType>(), true_state, busy_disabled::<K, T>());
    leads_to_stable_temp::<State<K, T>>(spec, lift_action(next::<K, T, ReconcilerType>()), true_pred(), lift_state(busy_disabled::<K, T>()));
}

pub proof fn lemma_any_pred_leads_to_crash_always_disabled<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, any_pred: TempPred<State<K, T>>
)
    requires
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(disable_crash().weak_fairness(())),
    ensures
        spec.entails(any_pred.leads_to(always(lift_state(crash_disabled::<K, T>())))),
{
    valid_implies_implies_leads_to::<State<K, T>>(spec, any_pred, true_pred());
    lemma_true_leads_to_crash_always_disabled::<K, T, ReconcilerType>(spec);
    leads_to_trans_temp::<State<K, T>>(spec, any_pred, true_pred(), always(lift_state(crash_disabled::<K, T>())));
}

pub open spec fn desired_state_is<K: ResourceView, T>(cr: K) -> StatePred<State<K, T>>
    recommends
        K::kind().is_CustomResourceKind(),
{
    |s: State<K, T>| {
        &&& s.resource_key_exists(cr.object_ref())
        &&& K::from_dynamic_object(s.resource_obj_of(cr.object_ref())).is_Ok()
        &&& K::from_dynamic_object(s.resource_obj_of(cr.object_ref())).get_Ok_0().spec() == cr.spec()
    }
}

}
