// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::{
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

proof fn lemma_true_leads_to_always_current_state_matches(fb: FluentBitView)
    requires
        fb.well_formed(),
    ensures
        assumption_and_invariants_of_all_phases(fb)
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(fb))))
        ),
{
    let spec = assumption_and_invariants_of_all_phases(fb);
    lemma_true_leads_to_state_matches_for_all_resources(fb);
    assert forall |sub_resource: SubResource| spec.entails(
        true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, fb))))
    ) by {
        use_tla_forall_for_sub_resource(spec, sub_resource, fb);
        lemma_resource_object_is_stable(spec, sub_resource, fb, true_pred());
    }
    leads_to_always_combine_n_with_equality!(
        spec, true_pred(), lift_state(current_state_matches(fb)),
        lift_state(sub_resource_state_matches(SubResource::ServiceAccount, fb)),
        lift_state(sub_resource_state_matches(SubResource::Role, fb)),
        lift_state(sub_resource_state_matches(SubResource::RoleBinding, fb)),
        lift_state(sub_resource_state_matches(SubResource::DaemonSet, fb))
    );
}

proof fn lemma_true_leads_to_state_matches_for_all_resources(fb: FluentBitView)
    requires
        fb.well_formed(),
    ensures
        forall |sub_resource: SubResource|
            assumption_and_invariants_of_all_phases(fb)
            .entails(
                true_pred().leads_to(lift_state(#[trigger] sub_resource_state_matches(sub_resource, fb)))
            ),
{
    let spec = assumption_and_invariants_of_all_phases(fb);

    assert forall |action: ActionKind, sub_resource: SubResource| #![auto]
    spec.entails(always(
        lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(action, sub_resource))))
    )) by {
        use_tla_forall(spec,
            |step: (ActionKind, SubResource)| always(
                lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(step.0, step.1))))
            ),
            (action, sub_resource)
        );
    }

    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, fb);
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(fb).

    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(spec, fb);
    lemma_from_scheduled_to_init_step(spec, fb);

    // After applying this lemma, we get spec |= init /\ no_pending_req ~> get_service_account /\ pending_req.
    lemma_from_init_step_to_after_get_service_account_step(spec, fb);

    // We first show that the reconciler can go to at_after_get_resource_step(next_resource) from at_after_get_resource_step(sub_resource)
    // where sub_resource cannot be DaemonSet because it's the last resource to be processed and doesn't have its next_resource.
    // Through this, we can string all the resources together in sequence. This also means that the system can go to any
    // at_after_get_resource_step(sub_resource) from an arbitrary state.
    assert forall |sub_resource: SubResource| sub_resource != SubResource::DaemonSet implies spec.entails(
        lift_state(#[trigger] pending_req_in_flight_at_after_get_resource_step(sub_resource, fb))
            .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource).get_AfterKRequestStep_1(), fb)))) by {
        use_tla_forall_for_sub_resource(spec, sub_resource, fb);
        let next_resource = next_resource_after(sub_resource).get_AfterKRequestStep_1();
        lemma_from_after_get_resource_step_to_resource_matches(spec, fb, sub_resource, next_resource);
    }
    // Thanks to the recursive construction of macro.
    leads_to_trans_n!(
        spec, true_pred(), lift_state(|s: FBCluster| { !s.ongoing_reconciles().contains_key(fb.object_ref()) }),
        lift_state(|s: FBCluster| { !s.ongoing_reconciles().contains_key(fb.object_ref()) && s.scheduled_reconciles().contains_key(fb.object_ref())}),
        lift_state(no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Role, fb)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::RoleBinding, fb)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::DaemonSet, fb))
    );

    // Since we already have true ~> at_after_get_resource_step(sub_resource), and we can get at_after_get_resource_step(sub_resource)
    // ~> sub_resource_state_matches(sub_resource, fb) by applying lemma lemma_from_after_get_resource_step_to_resource_matches,
    // we now have true ~> sub_resource_state_matches(sub_resource, fb).
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(lift_state(#[trigger] sub_resource_state_matches(sub_resource, fb)))) by {
        use_tla_forall_for_sub_resource(spec, sub_resource, fb);
        let next_resource = if sub_resource == SubResource::DaemonSet { sub_resource } else {
            next_resource_after(sub_resource).get_AfterKRequestStep_1()
        };
        lemma_from_after_get_resource_step_to_resource_matches(spec, fb, sub_resource, next_resource);
        leads_to_trans_temp(
            spec, true_pred(), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, fb)),
            lift_state(sub_resource_state_matches(sub_resource, fb))
        );
    }
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
        fb.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: FBCluster| { !s.ongoing_reconciles().contains_key(fb.object_ref()) })
                .leads_to(lift_state(|s: FBCluster| {
                    &&& !s.ongoing_reconciles().contains_key(fb.object_ref())
                    &&& s.scheduled_reconciles().contains_key(fb.object_ref())
                }))
        ),
{
    let pre = |s: FBCluster| {
        &&& !s.ongoing_reconciles().contains_key(fb.object_ref())
        &&& !s.scheduled_reconciles().contains_key(fb.object_ref())
    };
    let post = |s: FBCluster| {
        &&& !s.ongoing_reconciles().contains_key(fb.object_ref())
        &&& s.scheduled_reconciles().contains_key(fb.object_ref())
    };
    let input = fb.object_ref();
    FBCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(spec, input, FBCluster::next(), desired_state_is(fb), pre, post);
    valid_implies_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine(spec, pre, post, post);
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: FBCluster| {!s.ongoing_reconciles().contains_key(fb.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCluster::the_object_in_schedule_has_spec_and_uid_as(fb)))),
        fb.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: FBCluster| {
                &&& !s.ongoing_reconciles().contains_key(fb.object_ref())
                &&& s.scheduled_reconciles().contains_key(fb.object_ref())
            })
                .leads_to(lift_state(no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init)))
        ),
{
    let pre = |s: FBCluster| {
        &&& !s.ongoing_reconciles().contains_key(fb.object_ref())
        &&& s.scheduled_reconciles().contains_key(fb.object_ref())
    };
    let post = no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init);
    let input = (None, Some(fb.object_ref()));
    let stronger_next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
        &&& FBCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()(s)
        &&& FBCluster::the_object_in_schedule_has_spec_and_uid_as(fb)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::crash_disabled()),
        lift_state(FBCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::the_object_in_schedule_has_spec_and_uid_as(fb))
    );
    FBCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, FBCluster::run_scheduled_reconcile(), pre, post);
}

proof fn lemma_from_init_step_to_after_get_service_account_step(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
        spec.entails(always(lift_state(FBCluster::each_resp_matches_at_most_one_pending_req(fb.object_ref())))),
        spec.entails(always(lift_state(FBCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fb.object_ref())))),
        spec.entails(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        fb.well_formed(),
    ensures
        spec.entails(
            lift_state(no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb)))
        ),
{
    lemma_from_init_step_to_after_get_secret_step(spec, fb);
    assert_by(spec.entails(lift_state(pending_req_at_after_get_secret_step_with_fb(fb)).leads_to(lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)))), {
        let pre = |req_msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_secret_step(fb, req_msg));
        let post = lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb));
        assert forall |req_msg|
            spec.entails(#[trigger] pre(req_msg).leads_to(post))
        by {
            lemma_from_send_get_secret_req_to_receive_ok_resp_at_after_get_secret_step(spec, fb, req_msg);
        }
        leads_to_exists_intro(spec, pre, post);
        assert_by(tla_exists(pre) == lift_state(pending_req_at_after_get_secret_step_with_fb(fb)), {
            assert forall |ex| #[trigger] lift_state(pending_req_at_after_get_secret_step_with_fb(fb)).satisfied_by(ex)
            implies tla_exists(pre).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[fb.object_ref()].pending_req_msg.get_Some_0();
                assert(pre(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre), lift_state(pending_req_at_after_get_secret_step_with_fb(fb)));
        });
    });
    assert_by(spec.entails(lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb)))), {
        let pre = |resp_msg| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_secret_step(fb, resp_msg));
        let post = lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb));
        assert forall |resp_msg|
            spec.entails(#[trigger] pre(resp_msg).leads_to(post))
        by {
            lemma_from_after_get_secret_step_to_after_get_service_account_step(spec, fb, resp_msg);
        }
        leads_to_exists_intro(spec, pre, post);
        assert_by(tla_exists(pre) == lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)), {
            assert forall |ex| #[trigger] lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)).satisfied_by(ex)
            implies tla_exists(pre).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[fb.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                    &&& resp_msg.content.get_get_response().res.is_Ok()
                };
                assert(pre(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre), lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)));
        });
    });
    leads_to_trans_n!(spec,
        lift_state(no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init)),
        lift_state(pending_req_at_after_get_secret_step_with_fb(fb)),
        lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb))
    );
}

proof fn lemma_from_init_step_to_after_get_secret_step(
    spec: TempPred<FBCluster>, fb: FluentBitView
)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        fb.well_formed(),
    ensures
        spec.entails(
            lift_state(no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init))
                .leads_to(lift_state(pending_req_at_after_get_secret_step_with_fb(fb)))
        ),
{
    let pre = no_pending_req_at_fb_step_with_fb(fb, FluentBitReconcileStep::Init);
    let post = pending_req_at_after_get_secret_step_with_fb(fb);
    let input = (None, Some(fb.object_ref()));
    let stronger_next = |s, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(FBCluster::next()), lift_state(FBCluster::crash_disabled())
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| FBCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.1.get_Some_0() != fb.object_ref() {
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
    FBCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, FBCluster::continue_reconcile(), pre, post);
}

proof fn lemma_from_send_get_secret_req_to_receive_ok_resp_at_after_get_secret_step(
    spec: TempPred<FBCluster>, fb: FluentBitView, req_msg: FBMessage
)
    requires
        fb.well_formed(),
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_secret_step(fb, req_msg))
                .leads_to(lift_state(at_after_get_secret_step_and_exists_ok_resp_in_flight(fb)))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_get_secret_step(fb, req_msg);
    let post = at_after_get_secret_step_and_exists_ok_resp_in_flight(fb);
    let resource_key = get_secret_req(fb).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
        &&& FBCluster::busy_disabled()(s)
        &&& FBCluster::every_in_flight_msg_has_unique_id()(s)
        &&& desired_state_is(fb)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::crash_disabled()),
        lift_state(FBCluster::busy_disabled()),
        lift_state(FBCluster::every_in_flight_msg_has_unique_id()),
        lift_state(desired_state_is(fb))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| FBCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = FBCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Ok()
                        &&& resp_msg.content.get_get_response().res.get_Ok_0() == s_prime.resources()[resource_key]
                    });
                    assert(post(s_prime));
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && FBCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = FBCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == s_prime.resources()[resource_key]
        });
    }

    FBCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, FBCluster::handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_secret_step_to_after_get_service_account_step(
    spec: TempPred<FBCluster>, fb: FluentBitView, resp_msg: FBMessage
)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::each_resp_matches_at_most_one_pending_req(fb.object_ref())))),
        spec.entails(always(lift_state(FBCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fb.object_ref())))),
        spec.entails(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        fb.well_formed(),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_secret_step(fb, resp_msg))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb)))
        ),
{
    let pre = resp_msg_is_the_in_flight_ok_resp_at_after_get_secret_step(fb, resp_msg);
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, fb);
    let input = (Some(resp_msg), Some(fb.object_ref()));
    let stronger_next = |s, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
        &&& FBCluster::busy_disabled()(s)
        &&& FBCluster::each_resp_matches_at_most_one_pending_req(fb.object_ref())(s)
        &&& FBCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fb.object_ref())(s)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCluster::every_in_flight_msg_has_unique_id()(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::crash_disabled()),
        lift_state(FBCluster::busy_disabled()),
        lift_state(FBCluster::each_resp_matches_at_most_one_pending_req(fb.object_ref())),
        lift_state(FBCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fb.object_ref())),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCluster::every_in_flight_msg_has_unique_id())
    );

    FBCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        FBCluster::continue_reconcile(), pre, post
    );
}

proof fn use_tla_forall_for_sub_resource(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        fb.well_formed(),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, fb))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, fb))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(res, fb).key))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(res, fb).key))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(res, fb).key, fb))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, fb))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(res, fb).key, fb))))),
        spec.entails(tla_forall(|res: SubResource| always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, fb))))),
    ensures
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fb)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fb).key)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fb).key)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fb).key, fb)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fb)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, fb).key, fb)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fb)))),
{
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, fb))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, fb))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(res, fb).key))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(res, fb).key))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(res, fb).key, fb))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, fb))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(res, fb).key, fb))), sub_resource);
    use_tla_forall(spec, |res: SubResource| always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, fb))), sub_resource);
}

}
