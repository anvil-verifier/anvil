// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::{
    common::*,
    proof::{
        helper_invariants,
        liveness::{property::*, resource_match::*, spec::*, terminate},
        predicate::*,
        resource::*,
    },
    spec::{reconciler::*, resource::*, types::*},
};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

proof fn lemma_true_leads_to_always_current_state_matches(fbc: FluentBitConfigView)
    requires
        fbc.well_formed(),
    ensures
        assumption_and_invariants_of_all_phases(fbc)
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(fbc))))
        ),
{
    let spec = assumption_and_invariants_of_all_phases(fbc);
    lemma_true_leads_to_state_matches_for_all_resources(fbc);
    assert forall |sub_resource: SubResource| spec.entails(
        true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, fbc))))
    ) by {
        use_tla_forall_for_sub_resource(spec, sub_resource, fbc);
        lemma_resource_object_is_stable(spec, sub_resource, fbc, true_pred());
    }
    temp_pred_equality(lift_state(current_state_matches(fbc)), lift_state(sub_resource_state_matches(SubResource::Secret, fbc)));
}

proof fn lemma_true_leads_to_state_matches_for_all_resources(fbc: FluentBitConfigView)
    requires
        fbc.well_formed(),
    ensures
        forall |sub_resource: SubResource|
            assumption_and_invariants_of_all_phases(fbc)
            .entails(
                true_pred().leads_to(lift_state(#[trigger] sub_resource_state_matches(sub_resource, fbc)))
            ),
{
    let spec = assumption_and_invariants_of_all_phases(fbc);

    assert forall |action: ActionKind, sub_resource: SubResource| #![auto]
    spec.entails(always(
        lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(action, sub_resource))))
    )) by {
        use_tla_forall(spec,
            |step: (ActionKind, SubResource)| always(
                lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1))))
            ),
            (action, sub_resource)
        );
    }

    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, fbc);
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(fbc).

    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(spec, fbc);
    lemma_from_scheduled_to_init_step(spec, fbc);

    // After applying this lemma, we get spec |= init /\ no_pending_req ~> get_service_account /\ pending_req.
    lemma_from_init_step_to_after_get_secret_step(spec, fbc);

    use_tla_forall_for_sub_resource(spec, SubResource::Secret, fbc);
    lemma_from_after_get_resource_step_to_resource_matches(spec, fbc, SubResource::Secret, SubResource::Secret);
    leads_to_trans_n!(
        spec, true_pred(), lift_state(|s: FBCCluster| { !s.ongoing_reconciles().contains_key(fbc.object_ref()) }),
        lift_state(|s: FBCCluster| { !s.ongoing_reconciles().contains_key(fbc.object_ref()) && s.scheduled_reconciles().contains_key(fbc.object_ref())}),
        lift_state(no_pending_req_at_fbc_step_with_fbc(fbc, FluentBitConfigReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Secret, fbc)),
        lift_state(sub_resource_state_matches(SubResource::Secret, fbc))
    );
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fbc)))),
        fbc.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: FBCCluster| { !s.ongoing_reconciles().contains_key(fbc.object_ref()) })
                .leads_to(lift_state(|s: FBCCluster| {
                    &&& !s.ongoing_reconciles().contains_key(fbc.object_ref())
                    &&& s.scheduled_reconciles().contains_key(fbc.object_ref())
                }))
        ),
{
    let pre = |s: FBCCluster| {
        &&& !s.ongoing_reconciles().contains_key(fbc.object_ref())
        &&& !s.scheduled_reconciles().contains_key(fbc.object_ref())
    };
    let post = |s: FBCCluster| {
        &&& !s.ongoing_reconciles().contains_key(fbc.object_ref())
        &&& s.scheduled_reconciles().contains_key(fbc.object_ref())
    };
    let input = fbc.object_ref();
    FBCCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(spec, input, FBCCluster::next(), desired_state_is(fbc), pre, post);
    valid_implies_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine(spec, pre, post, post);
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: FBCCluster| {!s.ongoing_reconciles().contains_key(fbc.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::the_object_in_schedule_has_spec_and_uid_as(fbc)))),
        fbc.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: FBCCluster| {
                &&& !s.ongoing_reconciles().contains_key(fbc.object_ref())
                &&& s.scheduled_reconciles().contains_key(fbc.object_ref())
            })
                .leads_to(lift_state(no_pending_req_at_fbc_step_with_fbc(fbc, FluentBitConfigReconcileStep::Init)))
        ),
{
    let pre = |s: FBCCluster| {
        &&& !s.ongoing_reconciles().contains_key(fbc.object_ref())
        &&& s.scheduled_reconciles().contains_key(fbc.object_ref())
    };
    let post = no_pending_req_at_fbc_step_with_fbc(fbc, FluentBitConfigReconcileStep::Init);
    let input = (None, Some(fbc.object_ref()));
    let stronger_next = |s, s_prime| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()(s)
        &&& FBCCluster::the_object_in_schedule_has_spec_and_uid_as(fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(FBCCluster::the_object_in_schedule_has_spec_and_uid_as(fbc))
    );
    FBCCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, FBCCluster::run_scheduled_reconcile(), pre, post);
}

proof fn lemma_from_init_step_to_after_get_secret_step(
    spec: TempPred<FBCCluster>, fbc: FluentBitConfigView
)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        fbc.well_formed(),
    ensures
        spec.entails(
            lift_state(no_pending_req_at_fbc_step_with_fbc(fbc, FluentBitConfigReconcileStep::Init))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Secret, fbc)))
        ),
{
    let pre = no_pending_req_at_fbc_step_with_fbc(fbc, FluentBitConfigReconcileStep::Init);
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::Secret, fbc);
    let input = (None, Some(fbc.object_ref()));
    let stronger_next = |s, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(FBCCluster::next()), lift_state(FBCCluster::crash_disabled())
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| FBCCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.1.get_Some_0() != fbc.object_ref() {
                    assert(pre(s_prime));
                } else {
                    assert(post(s_prime));
                }
            },
            _ => {
                assert(pre(s_prime));
            }
        }
    }
    FBCCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, FBCCluster::continue_reconcile(), pre, post);
}

proof fn use_tla_forall_for_sub_resource(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        fbc.well_formed(),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, fbc))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, fbc))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(res, fbc).key))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(res, fbc).key))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(res, fbc).key, fbc))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, fbc))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(res, fbc).key, fbc))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, fbc))))),
    ensures
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, fbc).key, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)))),
{
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, fbc))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, fbc))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(res, fbc).key))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(res, fbc).key))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(res, fbc).key, fbc))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, fbc))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(res, fbc).key, fbc))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, fbc))), sub_resource);
}

}
