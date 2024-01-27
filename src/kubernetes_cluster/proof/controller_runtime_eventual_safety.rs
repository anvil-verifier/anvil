// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::spec::{common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::state_machine::*,
    controller::types::{ControllerAction, ControllerActionInput},
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn the_object_in_schedule_has_spec_and_uid_as(cr: K) -> StatePred<Self> {
    |s: Self| s.scheduled_reconciles().contains_key(cr.object_ref())
    ==> s.scheduled_reconciles()[cr.object_ref()].spec() == cr.spec()
    && s.scheduled_reconciles()[cr.object_ref()].metadata().uid == cr.metadata().uid
}

// This lemma says that under the spec where []desired_state_is(cr), it will eventually reach a state where any object
// in schedule for cr.object_ref() has the same spec as cr.spec.
pub proof fn lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(
    spec: TempPred<Self>, cr: K
)
    requires
        K::kind().is_CustomResourceKind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(Self::desired_state_is(cr)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::the_object_in_schedule_has_spec_and_uid_as(cr))))),
{
    let pre = |s: Self| true;
    let post = Self::the_object_in_schedule_has_spec_and_uid_as(cr);
    let input = cr.object_ref();
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::desired_state_is(cr)(s)
    };
    combine_spec_entails_always_n!(spec, lift_action(stronger_next), lift_action(Self::next()), lift_state(Self::desired_state_is(cr)));

    K::object_ref_is_well_formed();
    Self::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(
        spec, input, stronger_next, Self::desired_state_is(cr), pre, post
    );
    leads_to_stable_temp(spec, lift_action(stronger_next), lift_state(pre), lift_state(post));
}

pub open spec fn the_object_in_reconcile_has_spec_and_uid_as(cr: K) -> StatePred<Self> {
    |s: Self| s.ongoing_reconciles().contains_key(cr.object_ref()) ==>
    s.ongoing_reconciles()[cr.object_ref()].triggering_cr.spec() == cr.spec()
    && s.ongoing_reconciles()[cr.object_ref()].triggering_cr.metadata().uid == cr.metadata().uid
}

// This lemma says that under the spec where []desired_state_is(cr), it will eventually reach a state where any object
// in reconcile for cr.object_ref() has the same spec as cr.spec.
pub proof fn lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec: TempPred<Self>, cr: K)
    requires
        K::kind().is_CustomResourceKind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(Self::desired_state_is(cr)))),
        spec.entails(true_pred().leads_to(lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref())))),
        spec.entails(always(lift_state(Self::the_object_in_schedule_has_spec_and_uid_as(cr)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(cr))))),
{
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::the_object_in_schedule_has_spec_and_uid_as(cr)(s)
    };
    combine_spec_entails_always_n!(spec, lift_action(stronger_next), lift_action(Self::next()), lift_state(Self::the_object_in_schedule_has_spec_and_uid_as(cr)));

    let not_scheduled_or_reconcile = |s: Self| {
        &&& !s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& !s.scheduled_reconciles().contains_key(cr.object_ref())
    };
    let scheduled_and_not_reconcile = |s: Self| {
        &&& !s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.scheduled_reconciles().contains_key(cr.object_ref())
    };
    // Here we split the cases by whether s.scheduled_reconciles().contains_key(cr.object_ref()) is true
    assert_by(
        spec.entails(lift_state(not_scheduled_or_reconcile).leads_to(lift_state(scheduled_and_not_reconcile))),
        {
            let input = cr.object_ref();
            K::object_ref_is_well_formed();
            Self::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(
                spec, input, stronger_next, Self::desired_state_is(cr), not_scheduled_or_reconcile, scheduled_and_not_reconcile
            );
        }
    );
    assert_by(
        spec.entails(lift_state(scheduled_and_not_reconcile).leads_to(lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(cr)))),
        {
            let post = Self::the_object_in_reconcile_has_spec_and_uid_as(cr);
            let input = (None, Some(cr.object_ref()));
            K::object_ref_is_well_formed();
            Self::lemma_pre_leads_to_post_by_controller(
                spec, input, stronger_next, Self::run_scheduled_reconcile(), scheduled_and_not_reconcile, post
            );
        }
    );
    leads_to_trans_temp(spec, lift_state(not_scheduled_or_reconcile), lift_state(scheduled_and_not_reconcile), lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(cr)));
    let not_reconcile = |s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref());

    or_leads_to_combine_and_equality!(
        spec, lift_state(not_reconcile), lift_state(scheduled_and_not_reconcile), lift_state(not_scheduled_or_reconcile);
        lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(cr))
    );

    leads_to_trans_temp(
        spec, true_pred(), lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref())),
        lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(cr))
    );
    leads_to_stable_temp(spec, lift_action(stronger_next), true_pred(), lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(cr)));
}

}

}
