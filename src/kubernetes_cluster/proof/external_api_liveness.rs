// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::*, cluster::*, cluster_state_machine::Step,
    external_api::types::ExternalAPIAction, message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vstd_ext::multiset_lib::*;
use vstd::assert_multisets_equal;
use vstd::prelude::*;

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub proof fn lemma_pre_leads_to_post_by_external_api(
    spec: TempPred<Self>, input: Option<MsgType<E>>, next: ActionPred<Self>, action: ExternalAPIAction<E>, pre: StatePred<Self>, post: StatePred<Self>
)
    requires
        Self::external_api().actions.contains(action),
        forall |s, s_prime: Self| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: Self| pre(s) && #[trigger] next(s, s_prime) && Self::external_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: Self| #[trigger] pre(s) ==> Self::external_api_action_pre(action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
    ensures spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<Self, Option<MsgType<E>>>(spec, |i| Self::external_api_next().weak_fairness(i), input);
    Self::external_api_action_pre_implies_next_pre(action, input);
    valid_implies_trans::<Self>(
        lift_state(pre),
        lift_state(Self::external_api_action_pre(action, input)),
        lift_state(Self::external_api_next().pre(input))
    );
    Self::external_api_next().wf1(input, spec, next, pre, post);
}

}

}
