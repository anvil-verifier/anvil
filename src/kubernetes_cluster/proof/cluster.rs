// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    api_server::types::{ApiServerAction, ApiServerActionInput, ApiServerState},
    builtin_controllers::types::BuiltinControllerChoice,
    client,
    client::*,
    cluster::*,
    controller::state_machine::*,
    controller::types::{
        ControllerAction, ControllerActionInput, ControllerState, OngoingReconcile,
    },
    external_api::types::{ExternalAPIAction, ExternalAPIActionInput, ExternalAPIState},
    message::*,
    network::types::NetworkState,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

/// Prove weak_fairness is stable.
pub proof fn action_weak_fairness_is_stable<Output>(action: Action<Self, (), Output>)
    ensures
        valid(stable(action.weak_fairness(()))),
{
    let split_always = always(lift_state(action.pre(()))).implies(eventually(lift_action(action.forward(()))));
    always_p_is_stable::<Self>(split_always);
}

/// Prove weak_fairness for all input is stable.
pub proof fn tla_forall_action_weak_fairness_is_stable<Input, Output>(
    action: Action<Self, Input, Output>
)
    ensures
        valid(stable(tla_forall(|input| action.weak_fairness(input)))),
{
    let split_always = |input| always(lift_state(action.pre(input))).implies(eventually(lift_action(action.forward(input))));
    tla_forall_always_equality_variant::<Self, Input>(|input| action.weak_fairness(input), split_always);
    always_p_is_stable::<Self>(tla_forall(split_always));
}

pub proof fn lemma_true_leads_to_crash_always_disabled(
    spec: TempPred<Self>,
)
    requires
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(Self::disable_crash().weak_fairness(())),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::crash_disabled())))),
{
    let true_state = |s: Self| true;
    Self::disable_crash().wf1((), spec, Self::next(), true_state, Self::crash_disabled());
    leads_to_stable_temp::<Self>(spec, lift_action(Self::next()), true_pred(), lift_state(Self::crash_disabled()));
}

pub proof fn lemma_true_leads_to_busy_always_disabled(
    spec: TempPred<Self>,
)
    requires
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(Self::disable_transient_failure().weak_fairness(())),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::busy_disabled())))),
{
    let true_state = |s: Self| true;
    Self::disable_transient_failure().wf1((), spec, Self::next(), true_state, Self::busy_disabled());
    leads_to_stable_temp::<Self>(spec, lift_action(Self::next()), true_pred(), lift_state(Self::busy_disabled()));
}

pub proof fn lemma_any_pred_leads_to_crash_always_disabled(
    spec: TempPred<Self>, any_pred: TempPred<Self>
)
    requires
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(Self::disable_crash().weak_fairness(())),
    ensures spec.entails(any_pred.leads_to(always(lift_state(Self::crash_disabled())))),
{
    valid_implies_implies_leads_to::<Self>(spec, any_pred, true_pred());
    Self::lemma_true_leads_to_crash_always_disabled(spec);
    leads_to_trans_temp::<Self>(spec, any_pred, true_pred(), always(lift_state(Self::crash_disabled())));
}

// This desired_state_is specifies the desired state (described in the cr object)
// Informally, it says that given the cr object, the object's key exists in the etcd,
// and the corresponding object in etcd has the same spec and uid of the given cr object.
// Note that we also mention the name and namespace here, which seems a bit redundant
// because it seems that lemma_always_each_object_in_etcd_is_well_formed is enough
// to tell us the name/namespace are the same between the two. Unfortunately that's not true,
// and the reason is that given option1.get_Some_0() == option2.get_Some_0() and option1.is_Some(),
// Verus cannot induce that option1.is_Some() && option1 == option2.
// So it is necessary to say both the name and namespace are also the same.
pub open spec fn desired_state_is(cr: K) -> StatePred<Self>
    recommends
        K::kind().is_CustomResourceKind(),
{
    |s: Self| {
        &&& s.resources().contains_key(cr.object_ref())
        &&& K::unmarshal(s.resources()[cr.object_ref()]).is_Ok()
        &&& K::unmarshal(s.resources()[cr.object_ref()]).get_Ok_0().spec() == cr.spec()
        &&& K::unmarshal(s.resources()[cr.object_ref()]).get_Ok_0().metadata().name == cr.metadata().name
        &&& K::unmarshal(s.resources()[cr.object_ref()]).get_Ok_0().metadata().namespace == cr.metadata().namespace
        &&& K::unmarshal(s.resources()[cr.object_ref()]).get_Ok_0().metadata().uid == cr.metadata().uid
    }
}

}

}
