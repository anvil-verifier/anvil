// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    client,
    client::{client, ClientActionInput, ClientState},
    cluster::*,
    controller::common::{
        ControllerAction, ControllerActionInput, ControllerState, OngoingReconcile,
    },
    controller::state_machine::controller,
    external_api::*,
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
pub proof fn action_weak_fairness_is_stable<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>, Output>(action: Action<State<K, E, R>, (), Output>)
    ensures
        valid(stable(action.weak_fairness(()))),
{
    let split_always = always(lift_state(action.pre(()))).implies(eventually(lift_action(action.forward(()))));
    always_p_is_stable::<State<K, E, R>>(split_always);
}

/// Prove weak_fairness for all input is stable.
pub proof fn tla_forall_action_weak_fairness_is_stable<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>, Input, Output>(
    action: Action<State<K, E, R>, Input, Output>
)
    ensures
        valid(stable(tla_forall(|input| action.weak_fairness(input)))),
{
    let split_always = |input| always(lift_state(action.pre(input))).implies(eventually(lift_action(action.forward(input))));
    tla_forall_always_equality_variant::<State<K, E, R>, Input>(|input| action.weak_fairness(input), split_always);
    always_p_is_stable::<State<K, E, R>>(tla_forall(split_always));
}

/// Prove partial_spec is stable.
pub proof fn sm_partial_spec_is_stable<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>()
    ensures
        valid(stable(sm_partial_spec::<K, E, R>())),
{
    always_p_is_stable::<State<K, E, R>>(lift_action(next::<K, E, R>()));
    tla_forall_action_weak_fairness_is_stable::<K, E, R, Option<Message>, ()>(kubernetes_api_next());
    tla_forall_action_weak_fairness_is_stable::<K, E, R, (Option<Message>, Option<ExternalComm<E::Input, E::Output>>, Option<ObjectRef>), ()>(controller_next::<K, E, R>());
    tla_forall_action_weak_fairness_is_stable::<K, E, R, ExternalComm<E::Input, E::Output>, ()>(external_api_next::<K, E, R>());
    tla_forall_action_weak_fairness_is_stable::<K, E, R, ObjectRef, ()>(schedule_controller_reconcile());
    action_weak_fairness_is_stable::<K, E, R, ()>(disable_crash());
    action_weak_fairness_is_stable::<K, E, R, ()>(disable_busy());

    stable_and_n!(
        always(lift_action(next::<K, E, R>())),
        tla_forall(|input| kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| controller_next::<K, E, R>().weak_fairness(input)),
        tla_forall(|input| external_api_next::<K, E, R>().weak_fairness(input)),
        tla_forall(|input| schedule_controller_reconcile().weak_fairness(input)),
        disable_crash().weak_fairness(()),
        disable_busy().weak_fairness(())
    );
}

pub proof fn lemma_true_leads_to_crash_always_disabled<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>,
)
    requires
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(disable_crash().weak_fairness(())),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(crash_disabled::<K, E, R>())))),
{
    let true_state = |s: State<K, E, R>| true;
    disable_crash().wf1((), spec, next::<K, E, R>(), true_state, crash_disabled::<K, E, R>());
    leads_to_stable_temp::<State<K, E, R>>(spec, lift_action(next::<K, E, R>()), true_pred(), lift_state(crash_disabled::<K, E, R>()));
}

pub proof fn lemma_true_leads_to_busy_always_disabled<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>,
)
    requires
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(disable_busy().weak_fairness(())),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(busy_disabled::<K, E, R>())))),
{
    let true_state = |s: State<K, E, R>| true;
    disable_busy().wf1((), spec, next::<K, E, R>(), true_state, busy_disabled::<K, E, R>());
    leads_to_stable_temp::<State<K, E, R>>(spec, lift_action(next::<K, E, R>()), true_pred(), lift_state(busy_disabled::<K, E, R>()));
}

pub proof fn lemma_any_pred_leads_to_crash_always_disabled<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>, any_pred: TempPred<State<K, E, R>>
)
    requires
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(disable_crash().weak_fairness(())),
    ensures
        spec.entails(any_pred.leads_to(always(lift_state(crash_disabled::<K, E, R>())))),
{
    valid_implies_implies_leads_to::<State<K, E, R>>(spec, any_pred, true_pred());
    lemma_true_leads_to_crash_always_disabled::<K, E, R>(spec);
    leads_to_trans_temp::<State<K, E, R>>(spec, any_pred, true_pred(), always(lift_state(crash_disabled::<K, E, R>())));
}

pub open spec fn desired_state_is<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(cr: K) -> StatePred<State<K, E, R>>
    recommends
        K::kind().is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        &&& s.resource_key_exists(cr.object_ref())
        &&& K::from_dynamic_object(s.resource_obj_of(cr.object_ref())).is_Ok()
        &&& K::from_dynamic_object(s.resource_obj_of(cr.object_ref())).get_Ok_0().spec() == cr.spec()
    }
}

}
