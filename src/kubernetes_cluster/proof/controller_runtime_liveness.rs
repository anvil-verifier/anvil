// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::{
    proof::{
        controller_runtime::*, controller_runtime_safety,
        kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api, kubernetes_api_safety,
        wf1_assistant::controller_action_pre_implies_next_pre,
    },
    spec::{
        cluster::*,
        controller::common::{ControllerAction, ControllerActionInput},
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::controller,
        external_api::*,
        kubernetes_api::state_machine::{handle_request, transition_by_etcd},
        message::*,
    },
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

pub open spec fn partial_spec_with_always_cr_key_exists_and_crash_disabled
<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(cr_key: ObjectRef) -> TempPred<State<K, E, R>> {
    sm_partial_spec::<K, E, R>()
    .and(always(lift_state(|s: State<K, E, R>| {
        &&& s.resource_key_exists(cr_key)
        &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
    })))
    .and(always(lift_state(crash_disabled::<K, E, R>())))
}

pub proof fn lemma_pre_leads_to_post_by_controller<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>, input: (Option<Message>, Option<ExternalComm<E::Input, E::Output>>, Option<ObjectRef>), next: ActionPred<State<K, E, R>>,
    action: ControllerAction<K, E, R>, pre: StatePred<State<K, E, R>>, post: StatePred<State<K, E, R>>
)
    requires
        controller::<K, E, R>().actions.contains(action),
        forall |s, s_prime: State<K, E, R>| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<K, E, R>| pre(s) && #[trigger] next(s, s_prime) && controller_next::<K, E, R>().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<K, E, R>| #[trigger] pre(s) ==> controller_action_pre::<K, E, R>(action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| controller_next::<K, E, R>().weak_fairness(i))),
    ensures
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<K, E, R>, (Option<Message>, Option<ExternalComm<E::Input, E::Output>>, Option<ObjectRef>)>(
        spec, |i| controller_next::<K, E, R>().weak_fairness(i), input
    );

    controller_action_pre_implies_next_pre::<K, E, R>(action, input);
    valid_implies_trans::<State<K, E, R>>(
        lift_state(pre),
        lift_state(controller_action_pre::<K, E, R>(action, input)),
        lift_state(controller_next::<K, E, R>().pre(input))
    );

    controller_next::<K, E, R>().wf1(input, spec, next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_by_schedule_controller_reconcile<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>, input: ObjectRef, next: ActionPred<State<K, E, R>>,
    pre: StatePred<State<K, E, R>>, post: StatePred<State<K, E, R>>
)
    requires
        forall |s, s_prime: State<K, E, R>| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<K, E, R>| pre(s) && #[trigger] next(s, s_prime) && schedule_controller_reconcile::<K, E, R>().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<K, E, R>| #[trigger] pre(s) ==> schedule_controller_reconcile::<K, E, R>().pre(input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| schedule_controller_reconcile::<K, E, R>().weak_fairness(i))),
    ensures
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<K, E, R>, ObjectRef>(
        spec, |i| schedule_controller_reconcile::<K, E, R>().weak_fairness(i), input
    );
    schedule_controller_reconcile::<K, E, R>().wf1(input, spec, next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>, input: ObjectRef, next: ActionPred<State<K, E, R>>,
    c: StatePred<State<K, E, R>>, pre: StatePred<State<K, E, R>>, post: StatePred<State<K, E, R>>
)
    requires
        forall |s, s_prime: State<K, E, R>| pre(s) && c(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<K, E, R>| pre(s) && c(s) && #[trigger] next(s, s_prime) && schedule_controller_reconcile::<K, E, R>().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<K, E, R>| #[trigger] pre(s) && c(s) ==> schedule_controller_reconcile::<K, E, R>().pre(input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| schedule_controller_reconcile::<K, E, R>().weak_fairness(i))),
        spec.entails(always(lift_state(c))),
    ensures
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<K, E, R>, ObjectRef>(
        spec, |i| schedule_controller_reconcile::<K, E, R>().weak_fairness(i), input
    );
    schedule_controller_reconcile::<K, E, R>().wf1_borrow_from_spec(input, spec, next, c, pre, post);
}

pub proof fn lemma_reconcile_done_leads_to_reconcile_idle
<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(spec: TempPred<State<K, E, R>>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(tla_forall(|i| controller_next::<K, E, R>().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(reconciler_reconcile_done::<K, E, R>(cr_key))
                .leads_to(lift_state(|s: State<K, E, R>| {
                    &&& !s.reconcile_state_contains(cr_key)
                }))
        ),
{
    let pre = reconciler_reconcile_done::<K, E, R>(cr_key);
    let post = |s: State<K, E, R>| {
        &&& !s.reconcile_state_contains(cr_key)
    };
    let input = (Option::None, Option::None, Option::Some(cr_key));
    lemma_pre_leads_to_post_by_controller::<K, E, R>(
        spec, input, next::<K, E, R>(),
        end_reconcile::<K, E, R>(), pre, post
    );
}

pub proof fn lemma_reconcile_error_leads_to_reconcile_idle
<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(spec: TempPred<State<K, E, R>>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(tla_forall(|i| controller_next::<K, E, R>().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(reconciler_reconcile_error::<K, E, R>(cr_key))
                .leads_to(lift_state(|s: State<K, E, R>| {
                    &&& !s.reconcile_state_contains(cr_key)
                }))
        ),
{
    let pre = reconciler_reconcile_error::<K, E, R>(cr_key);
    let post = |s: State<K, E, R>| { !s.reconcile_state_contains(cr_key) };
    let input = (Option::None, Option::None, Option::Some(cr_key));
    lemma_pre_leads_to_post_by_controller::<K, E, R>(
        spec, input,
        next::<K, E, R>(), end_reconcile::<K, E, R>(), pre, post
    );
}

pub proof fn lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init
<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(spec: TempPred<State<K, E, R>>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(always(lift_state(crash_disabled::<K, E, R>()))),
        spec.entails(tla_forall(|i| controller_next::<K, E, R>().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<K, E, R>| {
                &&& !s.reconcile_state_contains(cr_key)
                &&& s.reconcile_scheduled_for(cr_key)
            })
                .leads_to(lift_state(reconciler_init_and_no_pending_req::<K, E, R>(cr_key)))
        ),
{
    let pre = |s: State<K, E, R>| {
        &&& !s.reconcile_state_contains(cr_key)
        &&& s.reconcile_scheduled_for(cr_key)
    };
    let post = reconciler_init_and_no_pending_req::<K, E, R>(cr_key);
    let stronger_next = |s, s_prime: State<K, E, R>| {
        &&& next::<K, E, R>()(s, s_prime)
        &&& !s.crash_enabled
    };
    strengthen_next::<State<K, E, R>>(spec, next::<K, E, R>(), crash_disabled::<K, E, R>(), stronger_next);
    let input = (Option::None, Option::None, Option::Some(cr_key));
    lemma_pre_leads_to_post_by_controller::<K, E, R>(
        spec, input, stronger_next, run_scheduled_reconcile::<K, E, R>(), pre, post
    );
}

pub proof fn lemma_true_leads_to_reconcile_scheduled_by_assumption<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>, cr_key: ObjectRef
)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_state(|s: State<K, E, R>| {
            &&& s.resource_key_exists(cr_key)
            &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
        }))),
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(tla_forall(|input| schedule_controller_reconcile().weak_fairness(input))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: State<K, E, R>| s.reconcile_scheduled_for(cr_key)))
        ),
{
    let cr_key_exists = |s: State<K, E, R>| {
        &&& s.resource_key_exists(cr_key)
        &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
    };
    let pre = |s: State<K, E, R>| true;
    let post = |s: State<K, E, R>| s.reconcile_scheduled_for(cr_key);
    let next_and_cr_exists = |s, s_prime: State<K, E, R>| {
        &&& next::<K, E, R>()(s, s_prime)
        &&& cr_key_exists(s)
    };
    strengthen_next::<State<K, E, R>>(spec, next::<K, E, R>(), cr_key_exists, next_and_cr_exists);
    temp_pred_equality::<State<K, E, R>>(lift_state(cr_key_exists), lift_state(schedule_controller_reconcile().pre(cr_key)));
    use_tla_forall::<State<K, E, R>, ObjectRef>(spec, |key| schedule_controller_reconcile().weak_fairness(key), cr_key);

    entails_and_temp(spec, always(lift_state(|s: State<K, E, R>| {
        &&& s.resource_key_exists(cr_key)
        &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
    })), always(lift_state(|s: State<K, E, R>| { cr_key.kind.is_CustomResourceKind() })));
    always_and_equality(lift_state(|s: State<K, E, R>| {
        &&& s.resource_key_exists(cr_key)
        &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
    }), lift_state(|s: State<K, E, R>| { cr_key.kind.is_CustomResourceKind() }));
    temp_pred_equality(lift_state(|s: State<K, E, R>| {
        &&& s.resource_key_exists(cr_key)
        &&& K::from_dynamic_object(s.resource_obj_of(cr_key)).is_Ok()
    }).and(lift_state(|s: State<K, E, R>| { cr_key.kind.is_CustomResourceKind() })), lift_state(pre).implies(lift_state(schedule_controller_reconcile::<K, E, R>().pre(cr_key))));

    schedule_controller_reconcile::<K, E, R>().wf1(cr_key, spec, next_and_cr_exists, pre, post);
}

pub proof fn lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>, cr: K, state: FnSpec(R::T) -> bool, next_state: FnSpec(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<K, E, R>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(cr.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(cr.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state(cr.object_ref(), state)))),
        forall |s| (#[trigger] state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s|
            state(s) ==>
            #[trigger] next_state(R::reconcile_core(cr_1, resp_o, s).0),
        spec.entails(
            lift_state(at_expected_reconcile_states(cr.object_ref(), next_state))
                .leads_to(lift_state(|s: State<K, E, R>| !s.reconcile_state_contains(cr.object_ref())))
        ),
    ensures
        spec.entails(
            lift_state(at_expected_reconcile_states(cr.object_ref(), state))
                .leads_to(lift_state(|s: State<K, E, R>| !s.reconcile_state_contains(cr.object_ref())))
        ),
{
    let at_some_state_and_pending_req_in_flight_or_resp_in_flight = |s: State<K, E, R>| {
        at_expected_reconcile_states(cr.object_ref(), state)(s)
        && pending_k8s_api_req_msg(s, cr.object_ref())
        && request_sent_by_controller(s.pending_req_of(cr.object_ref()))
        && (s.message_in_flight(s.pending_req_of(cr.object_ref()))
        || exists |resp_msg: Message| {
            #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(cr.object_ref()))
        })
    };
    temp_pred_equality::<State<K, E, R>>(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state(cr.object_ref(), state)), lift_state(at_expected_reconcile_states(cr.object_ref(), state)).implies(lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight)));
    implies_to_leads_to::<State<K, E, R>>(spec, lift_state(at_expected_reconcile_states(cr.object_ref(), state)), lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = pending_req_in_flight_at_reconcile_state(cr.object_ref(), state);
    let resp_in_flight = resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state);

    lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state::<K, E, R>(spec, cr, state, next_state);
    lemma_from_pending_req_in_flight_at_some_state_to_next_state::<K, E, R>(spec, cr, state, next_state);

    or_leads_to_combine(spec, req_in_flight, resp_in_flight, at_expected_reconcile_states(cr.object_ref(), next_state));
    temp_pred_equality::<State<K, E, R>>(
        lift_state(req_in_flight).or(lift_state(resp_in_flight)),
        lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight)
    );
    leads_to_trans_n!(
        spec,
        lift_state(at_expected_reconcile_states(cr.object_ref(), state)),
        lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(at_expected_reconcile_states(cr.object_ref(), next_state)),
        lift_state(|s: State<K, E, R>| !s.reconcile_state_contains(cr.object_ref()))
    );
}

pub proof fn lemma_from_init_state_to_next_state_to_reconcile_idle<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>, cr: K, init_state: FnSpec(R::T) -> bool, next_state: FnSpec(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(tla_forall(|i| controller_next::<K, E, R>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(pending_req_is_none_at_reconcile_state::<K, E, R>(cr.object_ref(), init_state)))),
        forall |s| (#[trigger] init_state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s|
            init_state(s) ==>
            next_state(#[trigger] R::reconcile_core(cr_1, resp_o, s).0),
        spec.entails(
            lift_state(at_expected_reconcile_states(cr.object_ref(), next_state))
                .leads_to(lift_state(|s: State<K, E, R>| !s.reconcile_state_contains(cr.object_ref())))
        ),
    ensures
        spec.entails(
            lift_state(at_expected_reconcile_states(cr.object_ref(), init_state))
                .leads_to(lift_state(|s: State<K, E, R>| !s.reconcile_state_contains(cr.object_ref())))
        ),
{
    let no_pending_req = |s: State<K, E, R>| {
        at_expected_reconcile_states(cr.object_ref(), init_state)(s)
        && no_pending_req_msg_or_external_api_input::<K, E, R>(s, cr.object_ref())
    };
    temp_pred_equality::<State<K, E, R>>(
        lift_state(pending_req_is_none_at_reconcile_state::<K, E, R>(cr.object_ref(), init_state)),
        lift_state(at_expected_reconcile_states(cr.object_ref(), init_state)).implies(lift_state(no_pending_req))
    );
    implies_to_leads_to(
        spec,
        lift_state(at_expected_reconcile_states(cr.object_ref(), init_state)),
        lift_state(no_pending_req)
    );
    let stronger_next = |s, s_prime: State<K, E, R>| {
        next::<K, E, R>()(s, s_prime)
        && !s.crash_enabled
    };
    strengthen_next(spec, next::<K, E, R>(), crash_disabled(), stronger_next);
    lemma_pre_leads_to_post_by_controller::<K, E, R>(
        spec, (Option::None, Option::None, Option::Some(cr.object_ref())),
        stronger_next,
        continue_reconcile::<K, E, R>(),
        no_pending_req,
        at_expected_reconcile_states(cr.object_ref(), next_state)
    );
    leads_to_trans_n!(
        spec,
        lift_state(at_expected_reconcile_states(cr.object_ref(), init_state)),
        lift_state(no_pending_req),
        lift_state(at_expected_reconcile_states(cr.object_ref(), next_state)),
        lift_state(|s: State<K, E, R>| !s.reconcile_state_contains(cr.object_ref()))
    );
}

pub proof fn lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>, cr: K, state: FnSpec(R::T) -> bool, next_state: FnSpec(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<K, E, R>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(cr.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(cr.object_ref())))),
        forall |s| (#[trigger] state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s|
            state(s) ==>
            #[trigger] next_state(R::reconcile_core(cr_1, resp_o, s).0),
    ensures
        spec.entails(
            lift_state(resp_in_flight_matches_pending_req_at_reconcile_state::<K, E, R>(cr.object_ref(), state))
                .leads_to(lift_state(at_expected_reconcile_states(cr.object_ref(), next_state)))
        ),
{
    let pre = resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state);
    let post = at_expected_reconcile_states(cr.object_ref(), next_state);
    let stronger_next = |s, s_prime: State<K, E, R>| {
        &&& next::<K, E, R>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(cr.object_ref())(s)
        &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(cr.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<K, E, R>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(cr.object_ref())),
        lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(cr.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<K, E, R>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(cr.object_ref())))
        .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(cr.object_ref())))
    );
    let known_resp_in_flight = |resp| lift_state(
        |s: State<K, E, R>| {
            at_expected_reconcile_states(cr.object_ref(), state)(s)
            && pending_k8s_api_req_msg(s, cr.object_ref())
            && request_sent_by_controller(s.pending_req_of(cr.object_ref()))
            && s.message_in_flight(resp)
            && resp_msg_matches_req_msg(resp, s.pending_req_of(cr.object_ref()))
        }
    );
    assert forall |msg: Message| spec.entails(#[trigger] known_resp_in_flight(msg)
        .leads_to(lift_state(post))) by {
            let resp_in_flight_state = |s: State<K, E, R>| {
                at_expected_reconcile_states(cr.object_ref(), state)(s)
                && pending_k8s_api_req_msg(s, cr.object_ref())
                && request_sent_by_controller(s.pending_req_of(cr.object_ref()))
                && s.message_in_flight(msg)
                && resp_msg_matches_req_msg(msg, s.pending_req_of(cr.object_ref()))
            };
            let input = (Option::Some(msg), Option::None, Option::Some(cr.object_ref()));
            lemma_pre_leads_to_post_by_controller::<K, E, R>(
                spec, input, stronger_next, continue_reconcile::<K, E, R>(), resp_in_flight_state, post
            );
    };
    leads_to_exists_intro::<State<K, E, R>, Message>(spec, known_resp_in_flight, lift_state(post));
    assert_by(
        tla_exists(known_resp_in_flight) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
            implies tla_exists(known_resp_in_flight).satisfied_by(ex) by {
                let s = ex.head();
                let msg = choose |resp_msg: Message| {
                    #[trigger] s.message_in_flight(resp_msg)
                    && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr.object_ref()).pending_req_msg.get_Some_0())
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
}

pub proof fn lemma_from_pending_req_in_flight_at_some_state_to_next_state<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>, cr: K, state: FnSpec(R::T) -> bool, next_state: FnSpec(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<K, E, R>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(cr.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(cr.object_ref())))),
        forall |s| (#[trigger] state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s|
            state(s) ==>
            #[trigger] next_state(R::reconcile_core(cr_1, resp_o, s).0),
    ensures
        spec.entails(
            lift_state(pending_req_in_flight_at_reconcile_state(cr.object_ref(), state))
                .leads_to(lift_state(at_expected_reconcile_states(cr.object_ref(), next_state)))
        ),
{
    let pre = pending_req_in_flight_at_reconcile_state(cr.object_ref(), state);
    assert forall |req_msg: Message| spec.entails(
        lift_state(#[trigger] req_msg_is_the_in_flight_pending_req_at_reconcile_state(cr.object_ref(), state, req_msg))
            .leads_to(lift_state(resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state)))
    ) by {
        let pre_1 = req_msg_is_the_in_flight_pending_req_at_reconcile_state(cr.object_ref(), state, req_msg);
        let post_1 = resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state);
        let stronger_next = |s, s_prime: State<K, E, R>| {
            &&& next::<K, E, R>()(s, s_prime)
            &&& crash_disabled()(s)
            &&& busy_disabled()(s)
            &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        };
        entails_always_and_n!(
            spec,
            lift_action(next::<K, E, R>()),
            lift_state(crash_disabled()),
            lift_state(busy_disabled()),
            lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())
        );
        temp_pred_equality(
            lift_action(stronger_next),
            lift_action(next::<K, E, R>())
            .and(lift_state(crash_disabled()))
            .and(lift_state(busy_disabled()))
            .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        );
        let input = Option::Some(req_msg);
        assert forall |s, s_prime: State<K, E, R>| pre_1(s) && #[trigger] stronger_next(s, s_prime)
        && kubernetes_api_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
            let resp_msg = transition_by_etcd(req_msg, s.kubernetes_api_state).1;
            assert({
                &&& s_prime.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            });
        };
        lemma_pre_leads_to_post_by_kubernetes_api::<K, E, R>(
            spec, input, stronger_next, handle_request(), pre_1, post_1
        );
    }
    let msg_2_temp = |msg| lift_state(req_msg_is_the_in_flight_pending_req_at_reconcile_state::<K, E, R>(cr.object_ref(), state, msg));
    leads_to_exists_intro(
        spec, msg_2_temp,
        lift_state(resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state))
    );
    assert_by(
        tla_exists(|msg| lift_state(req_msg_is_the_in_flight_pending_req_at_reconcile_state::<K, E, R>(cr.object_ref(), state, msg)))
        == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(cr.object_ref());
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
    lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state::<K, E, R>(spec, cr, state, next_state);
    leads_to_trans_n!(
        spec,
        lift_state(pre),
        lift_state(resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state)),
        lift_state(at_expected_reconcile_states(cr.object_ref(), next_state))
    );
}

pub proof fn lemma_from_some_state_with_ext_resp_to_two_next_states_to_reconcile_idle<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>>(
    spec: TempPred<State<K, E, R>>, cr: K, state: FnSpec(R::T) -> bool, next_state: FnSpec(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(next::<K, E, R>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<K, E, R>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(pending_req_is_none_at_reconcile_state(cr.object_ref(), state)))),
        forall |s| (#[trigger] state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s|
            state(s) ==> next_state(#[trigger] R::reconcile_core(cr_1, resp_o, s).0),
        spec.entails(
            lift_state(at_expected_reconcile_states(cr.object_ref(), next_state))
                .leads_to(lift_state(|s: State<K, E, R>| !s.reconcile_state_contains(cr.object_ref())))
        ),
    ensures
        spec.entails(
            lift_state(at_expected_reconcile_states(cr.object_ref(), state))
                .leads_to(lift_state(|s: State<K, E, R>| !s.reconcile_state_contains(cr.object_ref())))
        ),
{
    let no_req_at_state = |s: State<K, E, R>| {
        at_expected_reconcile_states(cr.object_ref(), state)(s)
        && no_pending_req_msg_or_external_api_input::<K, E, R>(s, cr.object_ref())
    };
    temp_pred_equality(lift_state(pending_req_is_none_at_reconcile_state(cr.object_ref(), state)), lift_state(at_expected_reconcile_states(cr.object_ref(), state)).implies(lift_state(no_req_at_state)));
    implies_to_leads_to(spec, lift_state(at_expected_reconcile_states(cr.object_ref(), state)), lift_state(no_req_at_state));

    let stronger_next = |s, s_prime: State<K, E, R>| {
        &&& next::<K, E, R>()(s, s_prime)
        &&& crash_disabled()(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<K, E, R>()),
        lift_state(crash_disabled())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<K, E, R>())
        .and(lift_state(crash_disabled()))
    );
    let input = (Option::None, Option::None, Option::Some(cr.object_ref()));
    lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, continue_reconcile(), no_req_at_state, at_expected_reconcile_states(cr.object_ref(), next_state));
    leads_to_trans_n!(
        spec,
        lift_state(at_expected_reconcile_states(cr.object_ref(), state)),
        lift_state(no_req_at_state),
        lift_state(at_expected_reconcile_states(cr.object_ref(), next_state)),
        lift_state(|s: State<K, E, R>| !s.reconcile_state_contains(cr.object_ref()))
    );
}

}
