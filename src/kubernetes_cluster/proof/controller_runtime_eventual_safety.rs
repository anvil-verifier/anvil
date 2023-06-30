// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, resource::*};
use crate::kubernetes_cluster::{
    proof::{
        cluster::*, cluster_safety, controller_runtime_liveness, kubernetes_api_safety,
        wf1_assistant::controller_action_pre_implies_next_pre,
    },
    spec::{
        cluster::*,
        controller::common::{ControllerAction, ControllerActionInput},
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

pub open spec fn the_object_in_schedule_has_spec_as<K: ResourceView, T>(cr: K) -> StatePred<State<K, T>> {
    |s: State<K, T>| s.reconcile_scheduled_for(cr.object_ref()) ==> s.reconcile_scheduled_obj_of(cr.object_ref()).spec() == cr.spec()
}

// This lemma says that under the spec where []desired_state_is(cr), it will eventually reach a state where any object
// in schedule for cr.object_ref() has the same spec as cr.spec.
pub proof fn lemma_true_leads_to_always_the_object_in_schedule_has_spec_as<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, cr: K
)
    requires
        K::kind().is_CustomResourceKind(),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(cr)))),
        spec.entails(always(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(the_object_in_schedule_has_spec_as(cr))))),
{
    let pre = |s: State<K, T>| true;
    let post = the_object_in_schedule_has_spec_as(cr);
    let input = cr.object_ref();
    let stronger_next = |s, s_prime: State<K, T>| {
        &&& next::<K, T, ReconcilerType>()(s, s_prime)
        &&& desired_state_is(cr)(s)
        &&& cluster_safety::each_object_in_etcd_is_well_formed()(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<K, T, ReconcilerType>()),
        lift_state(desired_state_is(cr)),
        lift_state(cluster_safety::each_object_in_etcd_is_well_formed())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<K, T, ReconcilerType>())
        .and(lift_state(desired_state_is(cr)))
        .and(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))
    );

    K::object_ref_is_well_formed();

    controller_runtime_liveness::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(
        spec, input, stronger_next, desired_state_is(cr), pre, post
    );
    leads_to_stable_temp(spec, lift_action(stronger_next), lift_state(pre), lift_state(post));
}

pub open spec fn the_object_in_reconcile_has_spec_as<K: ResourceView, T>(cr: K) -> StatePred<State<K, T>> {
    |s: State<K, T>| s.reconcile_state_contains(cr.object_ref()) ==> s.triggering_cr_of(cr.object_ref()).spec() == cr.spec()
}

// This lemma says that under the spec where []desired_state_is(cr), it will eventually reach a state where any object
// in reconcile for cr.object_ref() has the same spec as cr.spec.
pub proof fn lemma_true_leads_to_always_the_object_in_reconcile_has_spec_as<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, cr: K
)
    requires
        K::kind().is_CustomResourceKind(),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| controller_next::<K, T, ReconcilerType>().weak_fairness(i))),
        spec.entails(tla_forall(|i| schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(cr)))),
        spec.entails(true_pred().leads_to(lift_state(|s: State<K, T>| !s.reconcile_state_contains(cr.object_ref())))),
        spec.entails(true_pred().leads_to(always(lift_state(the_object_in_schedule_has_spec_as(cr))))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(the_object_in_reconcile_has_spec_as(cr))))),
{
    // We need to prepare a concrete spec which is stable because we will use unpack_conditions_from_spec later
    let stable_spec = always(lift_action(next::<K, T, ReconcilerType>()))
        .and(tla_forall(|i| schedule_controller_reconcile().weak_fairness(i)))
        .and(tla_forall(|i| controller_next::<K, T, ReconcilerType>().weak_fairness(i)))
        .and(always(lift_state(desired_state_is(cr))))
        .and(true_pred().leads_to(lift_state(|s: State<K, T>| !s.reconcile_state_contains(cr.object_ref()))))
        .and(true_pred().leads_to(always(lift_state(the_object_in_schedule_has_spec_as(cr)))));

    let stable_spec_with_assumption = stable_spec.and(always(lift_state(the_object_in_schedule_has_spec_as(cr))));

    // Let's first prove true ~> []the_object_in_reconcile_has_spec_as(cr)
    assert_by(
        stable_spec_with_assumption
        .entails(
            true_pred().leads_to(always(lift_state(the_object_in_reconcile_has_spec_as(cr))))
        ),
        {
            let stronger_next = |s, s_prime: State<K, T>| {
                &&& next::<K, T, ReconcilerType>()(s, s_prime)
                &&& the_object_in_schedule_has_spec_as(cr)(s)
            };
            entails_always_and_n!(
                stable_spec_with_assumption,
                lift_action(next::<K, T, ReconcilerType>()),
                lift_state(the_object_in_schedule_has_spec_as(cr))
            );
            temp_pred_equality(
                lift_action(stronger_next),
                lift_action(next::<K, T, ReconcilerType>())
                .and(lift_state(the_object_in_schedule_has_spec_as(cr)))
            );

            // Here we split the cases by whether s.reconcile_scheduled_for(cr.object_ref()) is true
            assert_by(
                stable_spec_with_assumption
                .entails(
                    lift_state(|s: State<K, T>| {
                        &&& !s.reconcile_state_contains(cr.object_ref())
                        &&& s.reconcile_scheduled_for(cr.object_ref())
                    }).leads_to(lift_state(the_object_in_reconcile_has_spec_as(cr)))
                ),
                {
                    let pre = |s: State<K, T>| {
                        &&& !s.reconcile_state_contains(cr.object_ref())
                        &&& s.reconcile_scheduled_for(cr.object_ref())
                    };
                    let post = the_object_in_reconcile_has_spec_as(cr);
                    let input = (Option::None, Option::Some(cr.object_ref()));

                    K::object_ref_is_well_formed();
                    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<K, T, ReconcilerType>(
                        stable_spec_with_assumption, input, stronger_next,
                        run_scheduled_reconcile::<K, T, ReconcilerType>(), pre, post
                    );
                }
            );

            assert_by(
                stable_spec_with_assumption
                .entails(
                    lift_state(|s: State<K, T>| {
                        &&& !s.reconcile_state_contains(cr.object_ref())
                        &&& !s.reconcile_scheduled_for(cr.object_ref())
                    }).leads_to(lift_state(the_object_in_reconcile_has_spec_as(cr)))
                ),
                {
                    let pre = |s: State<K, T>| {
                        &&& !s.reconcile_state_contains(cr.object_ref())
                        &&& !s.reconcile_scheduled_for(cr.object_ref())
                    };
                    let post = |s: State<K, T>| {
                        &&& !s.reconcile_state_contains(cr.object_ref())
                        &&& s.reconcile_scheduled_for(cr.object_ref())
                    };
                    let input = cr.object_ref();

                    K::object_ref_is_well_formed();
                    controller_runtime_liveness::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(
                        stable_spec_with_assumption, input, stronger_next, desired_state_is(cr), pre, post
                    );
                    leads_to_trans_temp(stable_spec_with_assumption, lift_state(pre), lift_state(post), lift_state(the_object_in_reconcile_has_spec_as(cr)));
                }
            );

            or_leads_to_combine_temp(
                stable_spec_with_assumption,
                lift_state(|s: State<K, T>| {
                    &&& !s.reconcile_state_contains(cr.object_ref())
                    &&& s.reconcile_scheduled_for(cr.object_ref())
                }),
                lift_state(|s: State<K, T>| {
                    &&& !s.reconcile_state_contains(cr.object_ref())
                    &&& !s.reconcile_scheduled_for(cr.object_ref())
                }),
                lift_state(the_object_in_reconcile_has_spec_as(cr))
            );

            temp_pred_equality(
                lift_state(|s: State<K, T>| {
                    &&& !s.reconcile_state_contains(cr.object_ref())
                    &&& s.reconcile_scheduled_for(cr.object_ref())
                }).or(lift_state(|s: State<K, T>| {
                    &&& !s.reconcile_state_contains(cr.object_ref())
                    &&& !s.reconcile_scheduled_for(cr.object_ref())
                })),
                lift_state(|s: State<K, T>| !s.reconcile_state_contains(cr.object_ref()))
            );

            leads_to_trans_temp(
                stable_spec_with_assumption,
                true_pred(),
                lift_state(|s: State<K, T>| !s.reconcile_state_contains(cr.object_ref())),
                lift_state(the_object_in_reconcile_has_spec_as(cr))
            );
            leads_to_stable_temp(stable_spec_with_assumption, lift_action(stronger_next), true_pred(), lift_state(the_object_in_reconcile_has_spec_as(cr)));
        }
    );

    // By unpacking the conditions we will have: stable_spec |= []the_object_in_schedule_has_spec_as(cr) ~> []the_object_in_reconcile_has_spec_as(cr)
    assume(valid(stable(stable_spec)));
    unpack_conditions_from_spec(
        stable_spec,
        always(lift_state(the_object_in_schedule_has_spec_as(cr))),
        true_pred(),
        always(lift_state(the_object_in_reconcile_has_spec_as(cr)))
    );
    temp_pred_equality(true_pred().and(always(lift_state(the_object_in_schedule_has_spec_as::<K, T>(cr)))), always(lift_state(the_object_in_schedule_has_spec_as(cr))));

    leads_to_trans_temp(stable_spec, true_pred(), always(lift_state(the_object_in_schedule_has_spec_as(cr))), always(lift_state(the_object_in_reconcile_has_spec_as(cr))));

    // Because spec might be different from stable_spec, we need this extra step
    entails_and_n!(
        spec,
        always(lift_action(next::<K, T, ReconcilerType>())),
        tla_forall(|i| schedule_controller_reconcile().weak_fairness(i)),
        tla_forall(|i| controller_next::<K, T, ReconcilerType>().weak_fairness(i)),
        always(lift_state(desired_state_is(cr))),
        true_pred().leads_to(lift_state(|s: State<K, T>| !s.reconcile_state_contains(cr.object_ref()))),
        true_pred().leads_to(always(lift_state(the_object_in_schedule_has_spec_as(cr))))
    );
    entails_trans(spec, stable_spec, true_pred().leads_to(always(lift_state(the_object_in_reconcile_has_spec_as(cr)))));
}

}
