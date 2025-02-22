// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerAction, ControllerActionInput},
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub proof fn lemma_pre_leads_to_post_by_controller(
    spec: TempPred<Self>, input: (Option<MsgType<E>>, Option<ObjectRef>), next: ActionPred<Self>,
    action: ControllerAction<K, E, R>, pre: StatePred<Self>, post: StatePred<Self>
)
    requires
        Self::controller().actions.contains(action),
        forall |s, s_prime: Self| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: Self| pre(s) && #[trigger] next(s, s_prime) && Self::controller_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: Self| #[trigger] pre(s) ==> Self::controller_action_pre(action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
    ensures spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<Self, (Option<MsgType<E>>, Option<ObjectRef>)>(
        spec, |i| Self::controller_next().weak_fairness(i), input
    );

    Self::controller_action_pre_implies_next_pre(action, input);
    entails_trans::<Self>(
        lift_state(pre),
        lift_state(Self::controller_action_pre(action, input)),
        lift_state(Self::controller_next().pre(input))
    );

    Self::controller_next().wf1(input, spec, next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_by_schedule_controller_reconcile(
    spec: TempPred<Self>, input: ObjectRef, next: ActionPred<Self>,
    pre: StatePred<Self>, post: StatePred<Self>
)
    requires
        forall |s, s_prime: Self| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: Self| pre(s) && #[trigger] next(s, s_prime) && Self::schedule_controller_reconcile().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: Self| #[trigger] pre(s) ==> Self::schedule_controller_reconcile().pre(input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| Self::schedule_controller_reconcile().weak_fairness(i))),
    ensures spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<Self, ObjectRef>(
        spec, |i| Self::schedule_controller_reconcile().weak_fairness(i), input
    );
    Self::schedule_controller_reconcile().wf1(input, spec, next, pre, post);
}

pub proof fn lemma_reconcile_done_leads_to_reconcile_idle(spec: TempPred<Self>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        K::kind() == cr_key.kind,
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
    ensures spec.entails(lift_state(Self::reconciler_reconcile_done(cr_key)).leads_to(lift_state(|s: Self| { !s.ongoing_reconciles().contains_key(cr_key)}))),
{
    let pre = Self::reconciler_reconcile_done(cr_key);
    let post = |s: Self| {
        &&& !s.ongoing_reconciles().contains_key(cr_key)
    };
    let input = (None, Some(cr_key));
    Self::lemma_pre_leads_to_post_by_controller(
        spec, input, Self::next(),
        Self::end_reconcile(), pre, post
    );
}

pub proof fn lemma_reconcile_error_leads_to_reconcile_idle
(spec: TempPred<Self>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        K::kind() == cr_key.kind,
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
    ensures spec.entails(lift_state(Self::reconciler_reconcile_error(cr_key)).leads_to(lift_state(|s: Self| { !s.ongoing_reconciles().contains_key(cr_key) }))),
{
    let pre = Self::reconciler_reconcile_error(cr_key);
    let post = |s: Self| { !s.ongoing_reconciles().contains_key(cr_key) };
    let input = (None, Some(cr_key));
    Self::lemma_pre_leads_to_post_by_controller(
        spec, input,
        Self::next(), Self::end_reconcile(), pre, post
    );
}

pub proof fn lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init
(spec: TempPred<Self>, cr_key: ObjectRef)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        K::kind() == cr_key.kind,
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(always(lift_state(Self::crash_disabled()))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: Self| {
                &&& !s.ongoing_reconciles().contains_key(cr_key)
                &&& s.scheduled_reconciles().contains_key(cr_key)
            }).leads_to(lift_state(Self::reconciler_init_and_no_pending_req(cr_key)))
        ),
{
    let pre = |s: Self| {
        &&& !s.ongoing_reconciles().contains_key(cr_key)
        &&& s.scheduled_reconciles().contains_key(cr_key)
    };
    let post = Self::reconciler_init_and_no_pending_req(cr_key);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& !s.crash_enabled
    };
    strengthen_next::<Self>(spec, Self::next(), Self::crash_disabled(), stronger_next);
    let input = (None, Some(cr_key));
    Self::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next, Self::run_scheduled_reconcile(), pre, post
    );
}

pub proof fn lemma_true_leads_to_reconcile_scheduled_by_assumption(
    spec: TempPred<Self>, cr_key: ObjectRef
)
    requires
        K::kind().is_CustomResourceKind(),
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(always(lift_state(|s: Self| {
            &&& s.resources().contains_key(cr_key)
            &&& K::unmarshal(s.resources()[cr_key]).is_Ok()
        }))),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|input| Self::schedule_controller_reconcile().weak_fairness(input))),
    ensures spec.entails(true_pred().leads_to(lift_state(|s: Self| s.scheduled_reconciles().contains_key(cr_key)))),
{
    let cr_key_exists = |s: Self| {
        &&& s.resources().contains_key(cr_key)
        &&& K::unmarshal(s.resources()[cr_key]).is_Ok()
    };
    let pre = |s: Self| true;
    let post = |s: Self| s.scheduled_reconciles().contains_key(cr_key);
    let next_and_cr_exists = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& cr_key_exists(s)
    };
    strengthen_next::<Self>(spec, Self::next(), cr_key_exists, next_and_cr_exists);
    temp_pred_equality::<Self>(lift_state(cr_key_exists), lift_state(Self::schedule_controller_reconcile().pre(cr_key)));
    use_tla_forall::<Self, ObjectRef>(spec, |key| Self::schedule_controller_reconcile().weak_fairness(key), cr_key);

    entails_and_temp(spec, always(lift_state(|s: Self| {
        &&& s.resources().contains_key(cr_key)
        &&& K::unmarshal(s.resources()[cr_key]).is_Ok()
    })), always(lift_state(|s: Self| { cr_key.kind.is_CustomResourceKind() })));
    always_and_equality(lift_state(|s: Self| {
        &&& s.resources().contains_key(cr_key)
        &&& K::unmarshal(s.resources()[cr_key]).is_Ok()
    }), lift_state(|s: Self| { cr_key.kind.is_CustomResourceKind() }));
    temp_pred_equality(lift_state(|s: Self| {
        &&& s.resources().contains_key(cr_key)
        &&& K::unmarshal(s.resources()[cr_key]).is_Ok()
    }).and(lift_state(|s: Self| { cr_key.kind.is_CustomResourceKind() })), lift_state(pre).implies(lift_state(Self::schedule_controller_reconcile().pre(cr_key))));

    Self::schedule_controller_reconcile().wf1(cr_key, spec, next_and_cr_exists, pre, post);
}

pub proof fn lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
    spec: TempPred<Self>, cr: K, state: spec_fn(R::T) -> bool, next_state: spec_fn(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::crash_disabled()))),
        spec.entails(always(lift_state(Self::busy_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(cr.object_ref())))),
        spec.entails(always(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(cr.object_ref(), state)))),
        forall |s| (#[trigger] state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s|
            state(s) ==>
            #[trigger] next_state(R::reconcile_core(cr_1, resp_o, s).0),
        spec.entails(
            lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state))
                .leads_to(lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref())))
        ),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(cr.object_ref(), state)).leads_to(lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref())))),
{
    Self::lemma_from_some_state_to_arbitrary_next_state(spec, cr, state, next_state);
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), state)),
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state)),
        lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref()))
    );
}

pub proof fn lemma_from_some_state_to_arbitrary_next_state(
    spec: TempPred<Self>, cr: K, state: spec_fn(R::T) -> bool, next_state: spec_fn(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::crash_disabled()))),
        spec.entails(always(lift_state(Self::busy_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(cr.object_ref())))),
        spec.entails(always(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(cr.object_ref(), state)))),
        forall |s| (#[trigger] state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s|
            state(s) ==>
            #[trigger] next_state(R::reconcile_core(cr_1, resp_o, s).0),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(cr.object_ref(), state)).leads_to(lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state)))),
{
    let at_some_state_and_pending_req_in_flight_or_resp_in_flight = |s: Self| {
        Self::at_expected_reconcile_states(cr.object_ref(), state)(s)
        && Self::has_pending_req_msg(s, cr.object_ref())
        && Self::request_sent_by_controller(s.ongoing_reconciles()[cr.object_ref()].pending_req_msg.get_Some_0())
        && (s.in_flight().contains(s.ongoing_reconciles()[cr.object_ref()].pending_req_msg.get_Some_0())
        || exists |resp_msg: MsgType<E>| {
            #[trigger] s.in_flight().contains(resp_msg)
            && Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[cr.object_ref()].pending_req_msg.get_Some_0())
        })
    };
    temp_pred_equality::<Self>(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(cr.object_ref(), state)), lift_state(Self::at_expected_reconcile_states(cr.object_ref(), state)).implies(lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight)));
    always_implies_to_leads_to::<Self>(spec, lift_state(Self::at_expected_reconcile_states(cr.object_ref(), state)), lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = Self::pending_req_in_flight_at_reconcile_state(cr.object_ref(), state);
    let resp_in_flight = Self::resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state);

    Self::lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state(spec, cr, state, next_state);
    Self::lemma_from_pending_req_in_flight_at_some_state_to_next_state(spec, cr, state, next_state);

    or_leads_to_combine(spec, lift_state(req_in_flight), lift_state(resp_in_flight), lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state)));
    temp_pred_equality::<Self>(
        lift_state(req_in_flight).or(lift_state(resp_in_flight)),
        lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight)
    );
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), state)),
        lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state))
    );
}

pub proof fn lemma_from_init_state_to_next_state_to_reconcile_idle(
    spec: TempPred<Self>, cr: K, init_state: spec_fn(R::T) -> bool, next_state: spec_fn(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::crash_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::no_pending_req_msg_at_reconcile_state(cr.object_ref(), init_state)))),
        forall |s| (#[trigger] init_state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s|
            init_state(s) ==>
            next_state(#[trigger] R::reconcile_core(cr_1, resp_o, s).0),
        spec.entails(
            lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state))
                .leads_to(lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref())))
        ),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(cr.object_ref(), init_state)).leads_to(lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref())))),
{
    let no_pending_req = |s: Self| {
        Self::at_expected_reconcile_states(cr.object_ref(), init_state)(s)
        && Self::no_pending_req_msg(s, cr.object_ref())
    };
    temp_pred_equality::<Self>(
        lift_state(Self::no_pending_req_msg_at_reconcile_state(cr.object_ref(), init_state)),
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), init_state)).implies(lift_state(no_pending_req))
    );
    always_implies_to_leads_to(
        spec,
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), init_state)),
        lift_state(no_pending_req)
    );
    let stronger_next = |s, s_prime: Self| {
        Self::next()(s, s_prime)
        && !s.crash_enabled
    };
    strengthen_next(spec, Self::next(), Self::crash_disabled(), stronger_next);
    Self::lemma_pre_leads_to_post_by_controller(
        spec, (None, Some(cr.object_ref())),
        stronger_next, Self::continue_reconcile(), no_pending_req,
        Self::at_expected_reconcile_states(cr.object_ref(), next_state)
    );
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), init_state)),
        lift_state(no_pending_req),
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state)),
        lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref()))
    );
}

pub proof fn lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state(
    spec: TempPred<Self>, cr: K, state: spec_fn(R::T) -> bool, next_state: spec_fn(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::crash_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(cr.object_ref())))),
        forall |s| (#[trigger] state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s|
            state(s) ==>
            #[trigger] next_state(R::reconcile_core(cr_1, resp_o, s).0),
    ensures spec.entails(lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state)).leads_to(lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state)))),
{
    let pre = Self::resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state);
    let post = Self::at_expected_reconcile_states(cr.object_ref(), next_state);
    let known_resp_in_flight = |resp| lift_state(
        |s: Self| {
            Self::at_expected_reconcile_states(cr.object_ref(), state)(s)
            && Self::has_pending_req_msg(s, cr.object_ref())
            && Self::request_sent_by_controller(s.ongoing_reconciles()[cr.object_ref()].pending_req_msg.get_Some_0())
            && s.in_flight().contains(resp)
            && Message::resp_msg_matches_req_msg(resp, s.ongoing_reconciles()[cr.object_ref()].pending_req_msg.get_Some_0())
        }
    );
    assert forall |msg: MsgType<E>| spec.entails(#[trigger] known_resp_in_flight(msg).leads_to(lift_state(post))) by {
        let stronger_next = |s, s_prime: Self| {
            &&& Self::next()(s, s_prime)
            &&& Self::crash_disabled()(s)
            &&& Self::pending_req_of_key_is_unique_with_unique_id(cr.object_ref())(s)
            &&& Self::every_in_flight_msg_has_unique_id()(s)
        };
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(Self::next()),
            lift_state(Self::crash_disabled()),
            lift_state(Self::pending_req_of_key_is_unique_with_unique_id(cr.object_ref())),
            lift_state(Self::every_in_flight_msg_has_unique_id())
        );
        let resp_in_flight_state = |s: Self| {
            Self::at_expected_reconcile_states(cr.object_ref(), state)(s)
            && Self::has_pending_req_msg(s, cr.object_ref())
            && Self::request_sent_by_controller(s.ongoing_reconciles()[cr.object_ref()].pending_req_msg.get_Some_0())
            && s.in_flight().contains(msg)
            && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[cr.object_ref()].pending_req_msg.get_Some_0())
        };
        let input = (Some(msg), Some(cr.object_ref()));
        Self::lemma_pre_leads_to_post_by_controller(
            spec, input, stronger_next, Self::continue_reconcile(), resp_in_flight_state, post
        );
    };
    leads_to_exists_intro::<Self, MsgType<E>>(spec, known_resp_in_flight, lift_state(post));
    assert_by(
        tla_exists(known_resp_in_flight) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
            implies tla_exists(known_resp_in_flight).satisfied_by(ex) by {
                let s = ex.head();
                let msg = choose |resp_msg: MsgType<E>| {
                    #[trigger] s.in_flight().contains(resp_msg)
                    && Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[cr.object_ref()].pending_req_msg.get_Some_0())
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
}

pub proof fn lemma_from_pending_req_in_flight_at_some_state_to_next_state(
    spec: TempPred<Self>, cr: K, state: spec_fn(R::T) -> bool, next_state: spec_fn(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::crash_disabled()))),
        spec.entails(always(lift_state(Self::busy_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(cr.object_ref())))),
        forall |s| (#[trigger] state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s| state(s) ==> #[trigger] next_state(R::reconcile_core(cr_1, resp_o, s).0),
    ensures spec.entails(lift_state(Self::pending_req_in_flight_at_reconcile_state(cr.object_ref(), state)).leads_to(lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state)))),
{
    Self::lemma_from_pending_req_in_flight_at_some_state_to_in_flight_resp_matches_pending_req_at_some_state(spec, cr, state);
    Self::lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state(spec, cr, state, next_state);
    leads_to_trans_n!(
        spec,
        lift_state(Self::pending_req_in_flight_at_reconcile_state(cr.object_ref(), state)),
        lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state)),
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state))
    );
}

#[verifier(spinoff_prover)]
pub proof fn lemma_from_pending_req_in_flight_at_some_state_to_in_flight_resp_matches_pending_req_at_some_state(
    spec: TempPred<Self>, cr: K, state: spec_fn(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::crash_disabled()))),
        spec.entails(always(lift_state(Self::busy_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        forall |s| (#[trigger] state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
    ensures spec.entails(lift_state(Self::pending_req_in_flight_at_reconcile_state(cr.object_ref(), state)).leads_to(lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state)))),
{
    let pre = Self::pending_req_in_flight_at_reconcile_state(cr.object_ref(), state);
    assert forall |req_msg: MsgType<E>| spec.entails(
        lift_state(#[trigger] Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(cr.object_ref(), state, req_msg))
            .leads_to(lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state)))
    ) by {
        let pre_1 = Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(cr.object_ref(), state, req_msg);
        let post_1 = Self::resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state);
        let stronger_next = |s, s_prime: Self| {
            &&& Self::next()(s, s_prime)
            &&& Self::crash_disabled()(s)
            &&& Self::busy_disabled()(s)
            &&& Self::every_in_flight_msg_has_unique_id()(s)
        };
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(Self::next()),
            lift_state(Self::crash_disabled()),
            lift_state(Self::busy_disabled()),
            lift_state(Self::every_in_flight_msg_has_unique_id())
        );
        if req_msg.content.is_APIRequest() {
            let input = Some(req_msg);
            assert forall |s, s_prime: Self| pre_1(s) && #[trigger] stronger_next(s, s_prime)
            && Self::kubernetes_api_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
                let resp_msg = Self::transition_by_etcd(req_msg, s.kubernetes_api_state).1;
                assert({
                    &&& s_prime.in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                });
            };
//            assert forall |s, s_prime: Self| pre_1(s) && #[trigger] stronger_next(s, s_prime)
//            implies pre_1(s_prime) || post_1(s_prime) by {
//                let step = choose |step| Self::next_step(s, s_prime, step);
//                match step {
//                    Step::ApiServerStep(input) => {
//                        if input.get_Some_0() == req_msg {
////                            assert(post_1(s_prime));
//                        } else {
////                            assert(pre_1(s_prime));
//                        }
//                    }
////                    Step::ControllerStep(input) => { assert(pre_1(s_prime)); },
//                    _ => { assert(pre_1(s_prime)); }
//                }
//            };
            Self::lemma_pre_leads_to_post_by_kubernetes_api(
                spec, input, stronger_next, Self::handle_request(), pre_1, post_1
            );
        } else {
            let input = Some(req_msg);
            assert forall |s, s_prime: Self| pre_1(s) && #[trigger] stronger_next(s, s_prime)
            && Self::external_api_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
                let resp_msg = Self::handle_external_request_helper(req_msg, s.external_api_state, s.kubernetes_api_state.resources).1;
                assert({
                    &&& s_prime.in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                });
            };
//            assert forall |s, s_prime: Self| pre_1(s) && #[trigger] stronger_next(s, s_prime)
//            implies pre_1(s_prime) || post_1(s_prime) by {
//                let step = choose |step| Self::next_step(s, s_prime, step);
//                match step {
//                    Step::ExternalAPIStep(input) => {
//                        if input.get_Some_0() == req_msg {
////                            assert(post_1(s_prime));
//                        } else {
////                            assert(pre_1(s_prime));
//                        }
//                    }
////                    Step::ControllerStep(input) => { assert(pre_1(s_prime)); },
//                    _ => { assert(pre_1(s_prime)); }
//                }
//            };
            Self::lemma_pre_leads_to_post_by_external_api(
                spec, input, stronger_next, Self::handle_external_request(), pre_1, post_1
            );
        }
    }
    let msg_2_temp = |msg| lift_state(Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(cr.object_ref(), state, msg));
    leads_to_exists_intro(
        spec, msg_2_temp,
        lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(cr.object_ref(), state))
    );
    assert_by(
        tla_exists(|msg| lift_state(Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(cr.object_ref(), state, msg)))
        == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[cr.object_ref()].pending_req_msg.get_Some_0();
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
}

pub proof fn lemma_from_some_state_with_ext_resp_to_two_next_states_to_reconcile_idle(
    spec: TempPred<Self>, cr: K, state: spec_fn(R::T) -> bool, next_state: spec_fn(R::T) -> bool
)
    requires
        cr.object_ref().kind == K::kind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::crash_disabled()))),
        spec.entails(always(lift_state(Self::no_pending_req_msg_at_reconcile_state(cr.object_ref(), state)))),
        forall |s| (#[trigger] state(s)) ==> !R::reconcile_error(s) && !R::reconcile_done(s),
        forall |cr_1, resp_o, s|
            state(s) ==> next_state(#[trigger] R::reconcile_core(cr_1, resp_o, s).0),
        spec.entails(
            lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state))
                .leads_to(lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref())))
        ),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(cr.object_ref(), state)).leads_to(lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref())))),
{
    let no_req_at_state = |s: Self| {
        Self::at_expected_reconcile_states(cr.object_ref(), state)(s)
        && Self::no_pending_req_msg(s, cr.object_ref())
    };
    temp_pred_equality(lift_state(Self::no_pending_req_msg_at_reconcile_state(cr.object_ref(), state)), lift_state(Self::at_expected_reconcile_states(cr.object_ref(), state)).implies(lift_state(no_req_at_state)));
    always_implies_to_leads_to(spec, lift_state(Self::at_expected_reconcile_states(cr.object_ref(), state)), lift_state(no_req_at_state));

    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::crash_disabled()(s)
    };
    combine_spec_entails_always_n!(spec, lift_action(stronger_next), lift_action(Self::next()), lift_state(Self::crash_disabled()));
    let input = (None, Some(cr.object_ref()));
    Self::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, Self::continue_reconcile(), no_req_at_state, Self::at_expected_reconcile_states(cr.object_ref(), next_state));
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), state)),
        lift_state(no_req_at_state),
        lift_state(Self::at_expected_reconcile_states(cr.object_ref(), next_state)),
        lift_state(|s: Self| !s.ongoing_reconciles().contains_key(cr.object_ref()))
    );
}

}

}
