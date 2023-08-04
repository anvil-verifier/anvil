// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::{api_method::*, common::*, error::*, resource::*};
use crate::kubernetes_cluster::Cluster;
use crate::kubernetes_cluster::{
    proof::{controller_runtime::*, kubernetes_api_safety, wf1_assistant::*},
    spec::{
        cluster::*,
        controller::common::{ControllerAction, ControllerActionInput},
        controller::state_machine::*,
        kubernetes_api::state_machine::{handle_request, transition_by_etcd},
        message::*,
    },
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn every_in_flight_msg_has_lower_id_than_allocator() -> StatePred<State<K, E, R>> {
    |s: State<K, E, R>| {
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            ==> msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_lower_id_than_allocator
    ()
    ensures
        Self::sm_spec().entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
{
    let invariant = Self::every_in_flight_msg_has_lower_id_than_allocator();
    assert forall |s, s_prime: State<K, E, R>| invariant(s) && #[trigger] Self::next()(s, s_prime) implies
    invariant(s_prime) by {
        Self::next_preserves_every_in_flight_msg_has_lower_id_than_allocator(s, s_prime);
    };
    init_invariant::<State<K, E, R>>(Self::sm_spec(), Self::init(), Self::next(), invariant);
}

proof fn next_preserves_every_in_flight_msg_has_lower_id_than_allocator(
    s: State<K, E, R>, s_prime: State<K, E, R>
)
    requires
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s), Self::next()(s, s_prime),
    ensures
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s_prime),
{
    assert forall |msg: Message| #[trigger] s_prime.message_in_flight(msg) implies
    msg.content.get_rest_id() < s_prime.rest_id_allocator.rest_id_counter by {
        assert(s.rest_id_allocator.rest_id_counter <= s_prime.rest_id_allocator.rest_id_counter);
        if (s.message_in_flight(msg)) {
            assert(msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter);
        } else {
            match msg.content {
                MessageContent::APIRequest(_, _) => assert(s.rest_id_allocator.rest_id_counter < s_prime.rest_id_allocator.rest_id_counter),
                MessageContent::APIResponse(_, id) => {
                    let next_step = choose |step: Step<K, E>| Self::next_step(s, s_prime, step);
                    match next_step {
                        Step::KubernetesAPIStep(input) => {
                            let req_msg = input.get_Some_0();
                            assert(s.message_in_flight(req_msg));
                            assert(id == req_msg.content.get_req_id());
                        }
                        Step::KubernetesBusy(input) => {
                            let req_msg = input.get_Some_0();
                            assert(s.message_in_flight(req_msg));
                            assert(id == req_msg.content.get_req_id());
                        }
                        _ => assert(false),
                    }
                }
            }
        }
    };
}

pub open spec fn every_in_flight_req_is_unique() -> StatePred<State<K, E, R>> {
    |s: State<K, E, R>| {
        forall |msg: Message|
            msg.content.is_APIRequest() && #[trigger] s.message_in_flight(msg)
            ==> s.network_state.in_flight.count(msg) == 1
    }
}

pub proof fn lemma_always_every_in_flight_req_is_unique()
    ensures
        Self::sm_spec().entails(
            always(lift_state(Self::every_in_flight_req_is_unique()))
        ),
{
    let invariant = Self::every_in_flight_req_is_unique();
    let stronger_next = |s, s_prime: State<K, E, R>| {
        &&& Self::next()(s, s_prime)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator();
    strengthen_next::<State<K, E, R>>(
        Self::sm_spec(), Self::next(), Self::every_in_flight_msg_has_lower_id_than_allocator(), stronger_next
    );
    assert forall |s, s_prime: State<K, E, R>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies
    invariant(s_prime) by {
        assert forall |msg: Message| msg.content.is_APIRequest() && #[trigger] s_prime.message_in_flight(msg) implies
        s_prime.network_state.in_flight.count(msg) == 1 by {
            if (s.message_in_flight(msg)) {
                assert(s.network_state.in_flight.count(msg) == 1);
            }
        };
    };
    init_invariant::<State<K, E, R>>(Self::sm_spec(), Self::init(), stronger_next, invariant);
}

pub open spec fn every_in_flight_msg_has_unique_id() -> StatePred<State<K, E, R>> {
    |s: State<K, E, R>| {
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            ==> (
                forall |other_msg: Message|
                    #[trigger] s.message_in_flight(other_msg)
                    && msg != other_msg
                    ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()
            )
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_unique_id()
    ensures
        Self::sm_spec().entails(
            always(lift_state(Self::every_in_flight_msg_has_unique_id()))
        ),
{
    let invariant = Self::every_in_flight_msg_has_unique_id();
    let stronger_next = |s, s_prime: State<K, E, R>| {
        Self::next()(s, s_prime)
        && Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        && Self::every_in_flight_req_is_unique()(s)
    };
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator();
    Self::lemma_always_every_in_flight_req_is_unique();
    entails_always_and_n!(
        Self::sm_spec(),
        lift_action(Self::next()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_req_is_unique())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(Self::next())
            .and(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))
            .and(lift_state(Self::every_in_flight_req_is_unique()))
    );
    assert forall |s, s_prime: State<K, E, R>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies
    invariant(s_prime) by {
        Self::next_and_unique_lower_msg_id_preserves_in_flight_msg_has_unique_id(s, s_prime);
    };
    init_invariant::<State<K, E, R>>(Self::sm_spec(), Self::init(), stronger_next, invariant);
}

proof fn next_and_unique_lower_msg_id_preserves_in_flight_msg_has_unique_id(
    s: State<K, E, R>, s_prime: State<K, E, R>
)
    requires
        Self::next()(s, s_prime),
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Self::every_in_flight_req_is_unique()(s),
        Self::every_in_flight_msg_has_unique_id()(s), // the invariant
    ensures
        Self::every_in_flight_msg_has_unique_id()(s_prime),
{
    assert forall |msg: Message| #[trigger] s_prime.message_in_flight(msg) implies
    (forall |other_msg: Message| #[trigger] s_prime.message_in_flight(other_msg) && msg != other_msg
        ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()) by {
        assert forall |other_msg: Message| #[trigger] s_prime.message_in_flight(other_msg) && msg != other_msg implies
        msg.content.get_rest_id() != other_msg.content.get_rest_id() by {
            // At most one message will be added to the network_state.in_flight for each action.
            assert(s.message_in_flight(msg) || s.message_in_flight(other_msg));
            if (s.message_in_flight(msg) && s.message_in_flight(other_msg)) {
                assert(msg.content.get_rest_id() != other_msg.content.get_rest_id());
            } else {
                if (s.message_in_flight(msg)) {
                    Self::newly_added_msg_have_different_id_from_existing_ones(s, s_prime, msg, other_msg);
                } else {
                    Self::newly_added_msg_have_different_id_from_existing_ones(s, s_prime, other_msg, msg);
                }
            }
        }
    };
}

proof fn newly_added_msg_have_different_id_from_existing_ones(
    s: State<K, E, R>, s_prime: State<K, E, R>, msg_1: Message, msg_2: Message
)
    requires
        Self::next()(s, s_prime),
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Self::every_in_flight_req_is_unique()(s),
        s.message_in_flight(msg_1),
        !s.message_in_flight(msg_2),
        s_prime.message_in_flight(msg_1),
        s_prime.message_in_flight(msg_2),
        Self::every_in_flight_msg_has_unique_id()(s), // the invariant
    ensures
        msg_1.content.get_rest_id() != msg_2.content.get_rest_id(),
{
    if (msg_2.content.is_APIResponse()) {
        let next_step = choose |step: Step<K, E>| Self::next_step(s, s_prime, step);
        match next_step {
            Step::KubernetesAPIStep(input) => {
                let req_msg = input.get_Some_0();
                assert(s.network_state.in_flight.count(req_msg) <= 1);
                assert(msg_1.content.get_rest_id() != msg_2.content.get_rest_id());
            }
            Step::KubernetesBusy(input) => {
                let req_msg = input.get_Some_0();
                assert(s.network_state.in_flight.count(req_msg) <= 1);
                assert(msg_1.content.get_rest_id() != msg_2.content.get_rest_id());
            }
            _ => assert(false),
        }
    }
}

pub open spec fn req_in_flight_or_pending_at_controller(req_msg: Message, s: State<K, E, R>) -> bool {
    req_msg.content.is_APIRequest() && (s.message_in_flight(req_msg)
    || exists |cr_key: ObjectRef| (
        #[trigger] s.reconcile_state_contains(cr_key)
        && Self::pending_k8s_api_req_msg_is(s, cr_key, req_msg)
        && s.reconcile_state_of(cr_key).pending_external_api_input.is_None()
    ))
}

pub open spec fn pending_req_has_lower_req_id_than_allocator() -> StatePred<State<K, E, R>> {
    |s: State<K, E, R>| {
        forall |cr_key: ObjectRef|
            #[trigger] s.reconcile_state_contains(cr_key)
            && Self::pending_k8s_api_req_msg(s, cr_key)
            ==> s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0().content.get_req_id() < s.rest_id_allocator.rest_id_counter
    }
}

pub proof fn lemma_always_pending_req_has_lower_req_id_than_allocator()
    ensures
        Self::sm_spec().entails(always(lift_state(Self::pending_req_has_lower_req_id_than_allocator()))),
{
    let invariant = Self::pending_req_has_lower_req_id_than_allocator();
    init_invariant::<State<K, E, R>>(
        Self::sm_spec(), Self::init(), Self::next(), invariant
    );
}

pub open spec fn resp_matches_at_most_one_pending_req(
    resp_msg: Message, cr_key: ObjectRef
) -> StatePred<State<K, E, R>> {
    |s: State<K, E, R>| {
        s.reconcile_state_contains(cr_key)
        && Self::pending_k8s_api_req_msg(s, cr_key)
        && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
        ==> (
            forall |other_key: ObjectRef|
                #[trigger] s.reconcile_state_contains(other_key)
                && Self::pending_k8s_api_req_msg(s, other_key)
                && other_key != cr_key
                ==> !resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(other_key).pending_req_msg.get_Some_0())
            )
    }
}

pub open spec fn resp_if_matches_pending_req_then_no_other_resp_matches(
    resp_msg: Message, cr_key: ObjectRef
) -> StatePred<State<K, E, R>> {
    |s: State<K, E, R>| {
        s.reconcile_state_contains(cr_key)
        && s.message_in_flight(resp_msg)
        && Self::pending_k8s_api_req_msg(s, cr_key)
        && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
        ==> (
            forall |other_resp: Message| other_resp != resp_msg && #[trigger] s.message_in_flight(other_resp)
            ==> !resp_msg_matches_req_msg(other_resp, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
        )
    }
}

pub proof fn lemma_always_resp_if_matches_pending_req_then_no_other_resp_matches(
    resp_msg: Message, cr_key: ObjectRef
)
    ensures
        Self::sm_spec().entails(
            always(lift_state(Self::resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key)))
        ),
{
    implies_preserved_by_always::<State<K, E, R>>(
        Self::every_in_flight_msg_has_unique_id(), Self::resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key)
    );
    Self::lemma_always_every_in_flight_msg_has_unique_id();
    entails_trans::<State<K, E, R>>(
        Self::sm_spec(),
        always(lift_state(Self::every_in_flight_msg_has_unique_id())),
        always(lift_state(Self::resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key)))
    );
}

pub proof fn lemma_forall_always_resp_if_matches_pending_req_then_no_other_resp_matches(
    cr_key: ObjectRef
)
    ensures
        Self::sm_spec().entails(
            tla_forall(|resp_msg: Message| always(lift_state(Self::resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key))))
        ),
{
    let m_to_p = |msg| always(lift_state(Self::resp_if_matches_pending_req_then_no_other_resp_matches(msg, cr_key)));
    assert forall |msg| #[trigger] Self::sm_spec().entails(m_to_p(msg)) by {
        Self::lemma_always_resp_if_matches_pending_req_then_no_other_resp_matches(msg, cr_key);
    }
    spec_entails_tla_forall(Self::sm_spec(), m_to_p);
}

pub open spec fn each_resp_if_matches_pending_req_then_no_other_resp_matches(
    cr_key: ObjectRef
) -> StatePred<State<K, E, R>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        forall |resp_msg: Message|
            s.reconcile_state_contains(cr_key)
            && #[trigger] s.message_in_flight(resp_msg)
            && Self::pending_k8s_api_req_msg(s, cr_key)
            && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
            ==> (
                forall |other_resp: Message| other_resp != resp_msg && #[trigger] s.message_in_flight(other_resp)
                ==> !resp_msg_matches_req_msg(other_resp, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
            )
    }
}

pub proof fn lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches(
    cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        Self::sm_spec().entails(
            always(lift_state(Self::each_resp_if_matches_pending_req_then_no_other_resp_matches(cr_key)))
        ),
{
    let spec = Self::sm_spec();
    let forall_a_to_p = lift_state(Self::each_resp_if_matches_pending_req_then_no_other_resp_matches(cr_key));
    let a_to_p = |resp_msg: Message| lift_state(Self::resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key));
    let a_to_always_p = |resp_msg: Message| always(a_to_p(resp_msg));
    assert forall |resp_msg: Message| spec.entails(#[trigger] a_to_always_p(resp_msg))
    by {
        Self::lemma_always_resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key);
    }
    spec_entails_tla_forall(spec, a_to_always_p);
    tla_forall_always_equality(a_to_p);

    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies forall_a_to_p.satisfied_by(ex) by {
        assert forall |resp_msg: Message|
            ex.head().reconcile_state_contains(cr_key)
            && #[trigger] ex.head().message_in_flight(resp_msg)
            && Self::pending_k8s_api_req_msg(ex.head(), cr_key)
            && resp_msg_matches_req_msg(resp_msg, ex.head().reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
            ==> (
                forall |other_resp: Message| other_resp != resp_msg && #[trigger] ex.head().message_in_flight(other_resp)
                ==> !resp_msg_matches_req_msg(other_resp, ex.head().reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
            )
        by {
            assert(a_to_p(resp_msg).satisfied_by(ex));
        }
    }

    temp_pred_equality(forall_a_to_p, tla_forall(a_to_p));

}

pub proof fn lemma_always_resp_matches_at_most_one_pending_req(
    resp_msg: Message, cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        Self::sm_spec().entails(always(lift_state(Self::resp_matches_at_most_one_pending_req(resp_msg, cr_key)))),
{
    let invariant = Self::resp_matches_at_most_one_pending_req(resp_msg, cr_key);
    let stronger_next = |s, s_prime: State<K, E, R>| {
        &&& Self::next()(s, s_prime)
        &&& Self::pending_req_has_lower_req_id_than_allocator()(s)
    };

    Self::lemma_always_pending_req_has_lower_req_id_than_allocator();

    strengthen_next::<State<K, E, R>>(
        Self::sm_spec(), Self::next(), Self::pending_req_has_lower_req_id_than_allocator(), stronger_next
    );
    init_invariant::<State<K, E, R>>(Self::sm_spec(), Self::init(), stronger_next, invariant);
}

pub proof fn lemma_forall_resp_always_matches_at_most_one_pending_req(
    cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        Self::sm_spec().entails(
            tla_forall(|msg| always(lift_state(Self::resp_matches_at_most_one_pending_req(msg, cr_key))))
        ),
{
    let m_to_p = |msg| always(lift_state(Self::resp_matches_at_most_one_pending_req(msg, cr_key)));
    assert forall |msg| #[trigger] Self::sm_spec().entails(m_to_p(msg)) by {
        Self::lemma_always_resp_matches_at_most_one_pending_req(msg, cr_key);
    };
    spec_entails_tla_forall(Self::sm_spec(), m_to_p);
}

pub open spec fn each_resp_matches_at_most_one_pending_req(
    cr_key: ObjectRef
) -> StatePred<State<K, E, R>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<K, E, R>| {
        forall |resp_msg: Message|
            s.reconcile_state_contains(cr_key)
            && Self::pending_k8s_api_req_msg(s, cr_key)
            && #[trigger] resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
            ==> (
                forall |other_key: ObjectRef|
                    #[trigger] s.reconcile_state_contains(other_key)
                    && Self::pending_k8s_api_req_msg(s, other_key)
                    && other_key != cr_key
                    ==> !resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(other_key).pending_req_msg.get_Some_0())
                )
    }
}

pub proof fn lemma_always_each_resp_matches_at_most_one_pending_req(
    cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        Self::sm_spec().entails(always(lift_state(Self::each_resp_matches_at_most_one_pending_req(cr_key)))),
{
    let invariant = Self::each_resp_matches_at_most_one_pending_req(cr_key);
    let stronger_next = |s, s_prime: State<K, E, R>| {
        &&& Self::next()(s, s_prime)
        &&& Self::pending_req_has_lower_req_id_than_allocator()(s)
    };

    Self::lemma_always_pending_req_has_lower_req_id_than_allocator();

    strengthen_next::<State<K, E, R>>(
        Self::sm_spec(), Self::next(),
        Self::pending_req_has_lower_req_id_than_allocator(), stronger_next
    );
    init_invariant::<State<K, E, R>>(Self::sm_spec(), Self::init(), stronger_next, invariant);
}

// This lemma ensures that if a controller is at some reconcile state for a cr, there must be the pending request of the
// reconcile state in flight or a correponding response in flight.
// Obviously, this requires that when controller enters the 'state' in reconcile_core, there must be a request generated;
// otherwise, the pending request may not be there.
// The proof is very straightforward:
//   - Right after the controller enters 'state', the pending request is added to in_flight.
//   - If the pending request is processed by kubernetes api, there will be a response in flight.
//   - If the response is processed by the controller, the controller will create a new pending request in flight which
//   allows the invariant to still hold.
pub proof fn lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
    spec: TempPred<State<K, E, R>>, key: ObjectRef, state: FnSpec(R::T) -> bool
)
    requires
        forall |s| (#[trigger] state(s)) ==> s != R::reconcile_init_state(),
        forall |cr, resp_o, pre_state| #[trigger] state(R::reconcile_core(cr, resp_o, pre_state).0)
            ==> {
                let req = R::reconcile_core(cr, resp_o, pre_state).1;
                &&& req.is_Some()
                &&& req.get_Some_0().is_KRequest()
            },
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(always(lift_state(Self::each_resp_matches_at_most_one_pending_req(key)))),
    ensures
        spec.entails(
            always(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(key, state)))
        ),
{
    let invariant = Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(key, state);
    let stronger_next = |s, s_prime: State<K, E, R>| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_resp_matches_at_most_one_pending_req(key)(s)
    };
    assert forall |s, s_prime: State<K, E, R>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        if Self::at_expected_reconcile_states(key, state)(s_prime) {
            let next_step = choose |step| Self::next_step(s, s_prime, step);
            assert(!next_step.is_RestartController());
            let resp = choose |msg| {
                #[trigger] s.message_in_flight(msg)
                && resp_msg_matches_req_msg(msg, s.pending_req_of(key))
            };
            match next_step {
                Step::KubernetesAPIStep(input) => {
                    if input == Option::Some(s.pending_req_of(key)) {
                        let resp_msg = transition_by_etcd(s.pending_req_of(key), s.kubernetes_api_state).1;
                        assert(s_prime.message_in_flight(resp_msg));
                    } else {
                        if !s.message_in_flight(s.pending_req_of(key)) {
                            assert(s_prime.message_in_flight(resp));
                        }
                    }
                }
                Step::KubernetesBusy(input) => {
                    if input == Option::Some(s.pending_req_of(key)) {
                        let resp_msg = form_matched_resp_msg(s.pending_req_of(key), Result::Err(APIError::ServerTimeout));
                        assert(s_prime.message_in_flight(resp_msg));
                    } else {
                        if !s.message_in_flight(s.pending_req_of(key)) {
                            assert(s_prime.message_in_flight(resp));
                        }
                    }
                }
                Step::ControllerStep(input) => {
                    let cr_key = input.2.get_Some_0();
                    if cr_key != key {
                        if s.message_in_flight(s.pending_req_of(key)) {
                            assert(s_prime.message_in_flight(s_prime.pending_req_of(key)));
                        } else {
                            assert(s_prime.message_in_flight(resp));
                        }
                    } else {
                        assert(s_prime.message_in_flight(s_prime.pending_req_of(key)));
                    }
                }
                Step::ClientStep(input) => {
                    if s.message_in_flight(s.pending_req_of(key)) {
                        assert(s_prime.message_in_flight(s_prime.pending_req_of(key)));
                    } else {
                        assert(s_prime.message_in_flight(resp));
                    }
                }
                _ => {
                    assert(invariant(s_prime));
                }
            }
        }
    }
    strengthen_next::<State<K, E, R>>(spec, Self::next(), Self::each_resp_matches_at_most_one_pending_req(key), stronger_next);
    init_invariant::<State<K, E, R>>(spec, Self::init(), stronger_next, invariant);
}

pub proof fn lemma_always_no_pending_req_msg_or_external_api_input_at_reconcile_state(
    spec: TempPred<State<K, E, R>>, key: ObjectRef, state: FnSpec(R::T) -> bool
)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
        forall |cr, resp_o, pre_state|
            #[trigger] state(R::reconcile_core(cr, resp_o, pre_state).0)
            ==> R::reconcile_core(cr, resp_o, pre_state).1.is_None(),
    ensures
        spec.entails(always(lift_state(Self::no_pending_req_msg_or_external_api_input_at_reconcile_state(key, state)))),
{
    let invariant = Self::no_pending_req_msg_or_external_api_input_at_reconcile_state(key, state);
    assert forall |s, s_prime: State<K, E, R>| invariant(s) &&
    #[trigger] Self::next()(s, s_prime) implies invariant(s_prime) by {
        if s_prime.reconcile_state_contains(key) && state(s_prime.reconcile_state_of(key).local_state) {
            if s.controller_state == s_prime.controller_state {
                assert(s.reconcile_state_of(key).pending_req_msg.is_None());
                assert(s_prime.reconcile_state_of(key).pending_req_msg.is_None());
            } else {
                assert(s_prime.reconcile_state_of(key).pending_req_msg.is_None());
            }
        }
    }
    init_invariant(spec, Self::init(), Self::next(), invariant);
}

pub proof fn lemma_always_pending_req_msg_is_none_at_reconcile_state(
    spec: TempPred<State<K, E, R>>, key: ObjectRef, state: FnSpec(R::T) -> bool
)
    requires
        forall |cr, resp_o, pre_state| #[trigger] state(R::reconcile_core(cr, resp_o, pre_state).0)
            ==> {
                let req = R::reconcile_core(cr, resp_o, pre_state).1;
                req.is_None()
                || req.get_Some_0().is_ExternalRequest()
            },
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(
            always(lift_state(Self::pending_req_msg_is_none_at_reconcile_state(key, state)))
        ),
{
    let invariant = Self::pending_req_msg_is_none_at_reconcile_state(key, state);
    init_invariant(spec, Self::init(), Self::next(), invariant);
}

}

}
