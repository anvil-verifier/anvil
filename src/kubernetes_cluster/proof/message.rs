// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::{api_method::*, common::*, error::*, resource::*};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerAction, ControllerActionInput},
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn every_in_flight_msg_has_lower_id_than_allocator() -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            #[trigger] s.message_in_flight(msg)
            ==> msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
{
    let invariant = Self::every_in_flight_msg_has_lower_id_than_allocator();
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] Self::next()(s, s_prime) implies
    invariant(s_prime) by {
        Self::next_preserves_every_in_flight_msg_has_lower_id_than_allocator(s, s_prime);
    };
    init_invariant::<Self>(spec, Self::init(), Self::next(), invariant);
}

proof fn next_preserves_every_in_flight_msg_has_lower_id_than_allocator(
    s: Self, s_prime: Self
)
    requires
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s), Self::next()(s, s_prime),
    ensures
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s_prime),
{
    assert forall |msg: MsgType<E>| #[trigger] s_prime.message_in_flight(msg) implies
    msg.content.get_rest_id() < s_prime.rest_id_allocator.rest_id_counter by {
        assert(s.rest_id_allocator.rest_id_counter <= s_prime.rest_id_allocator.rest_id_counter);
        if (s.message_in_flight(msg)) {
            assert(msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter);
        } else {
            match msg.content {
                MessageContent::APIRequest(_, id) => {
                    assert(id == s.rest_id_allocator.rest_id_counter);
                    assert(s.rest_id_allocator.rest_id_counter < s_prime.rest_id_allocator.rest_id_counter)
                },
                MessageContent::APIResponse(_, id) => {
                    let next_step = choose |step: Step<MsgType<E>>| Self::next_step(s, s_prime, step);
                    match next_step {
                        Step::KubernetesAPIStep(input) => {
                            let req_msg = input.get_Some_0();
                            assert(s.message_in_flight(req_msg));
                            assert(id == req_msg.content.get_rest_id());
                        }
                        Step::KubernetesBusy(input) => {
                            let req_msg = input.get_Some_0();
                            assert(s.message_in_flight(req_msg));
                            assert(id == req_msg.content.get_rest_id());
                        }
                        _ => assert(false),
                    }
                },
                MessageContent::ExternalAPIRequest(_, id) => {
                    assert(id == s.rest_id_allocator.rest_id_counter);
                    assert(s.rest_id_allocator.rest_id_counter < s_prime.rest_id_allocator.rest_id_counter)
                },
                MessageContent::ExternalAPIResponse(_, id) => {
                    let next_step = choose |step: Step<MsgType<E>>| Self::next_step(s, s_prime, step);
                    match next_step {
                        Step::ExternalAPIStep(input) => {
                            let req_msg = input.get_Some_0();
                            assert(s.message_in_flight(req_msg));
                            assert(s.message_in_flight(req_msg) ==> req_msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter);
                            assert(id == req_msg.content.get_rest_id());
                            assert(id < s.rest_id_allocator.rest_id_counter);
                        }
                        _ => assert(false),
                    }
                },
            }
            assert(msg.content.get_rest_id() < s_prime.rest_id_allocator.rest_id_counter);
        }
    };
}

pub open spec fn every_in_flight_req_is_unique() -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            (msg.content.is_APIRequest() || msg.content.is_ExternalAPIRequest())
            && #[trigger] s.message_in_flight(msg)
            ==> s.network_state.in_flight.count(msg) == 1
    }
}

pub proof fn lemma_always_every_in_flight_req_is_unique(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(
            always(lift_state(Self::every_in_flight_req_is_unique()))
        ),
{
    let invariant = Self::every_in_flight_req_is_unique();
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    strengthen_next::<Self>(
        spec, Self::next(), Self::every_in_flight_msg_has_lower_id_than_allocator(), stronger_next
    );
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime) implies
    invariant(s_prime) by {
        assert forall |msg: MsgType<E>|
        (msg.content.is_APIRequest() || msg.content.is_ExternalAPIRequest()) && #[trigger] s_prime.message_in_flight(msg) implies
        s_prime.network_state.in_flight.count(msg) == 1 by {
            if (s.message_in_flight(msg)) {
                assert(s.network_state.in_flight.count(msg) == 1);
            }
        };
    };
    init_invariant::<Self>(spec, Self::init(), stronger_next, invariant);
}

pub open spec fn in_flight_or_pending_req_message(s: Self, msg: MsgType<E>) -> bool {
    msg.content.is_APIRequest()
    && (s.message_in_flight(msg)
    || (
        exists |key|
            #[trigger] s.reconcile_state_contains(key)
            && s.reconcile_state_of(key).pending_req_msg == Some(msg)
    ))
}

pub open spec fn every_in_flight_or_pending_req_msg_has_unique_id() -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            #[trigger] Self::in_flight_or_pending_req_message(s, msg)
            ==> (
                forall |other_msg: MsgType<E>|
                    #[trigger] Self::in_flight_or_pending_req_message(s, other_msg)
                    && msg != other_msg
                    ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()
            )
    }
}

pub proof fn lemma_always_every_in_flight_or_pending_req_msg_has_unique_id(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(
            always(lift_state(Self::every_in_flight_or_pending_req_msg_has_unique_id()))
        ),
{
    let invariant = Self::every_in_flight_or_pending_req_msg_has_unique_id();
    let stronger_next = |s, s_prime: Self| {
        Self::next()(s, s_prime)
        && Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        && Self::pending_req_has_lower_req_id_than_allocator()(s)
    };
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    Self::lemma_always_pending_req_has_lower_req_id_than_allocator(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::pending_req_has_lower_req_id_than_allocator())
    );
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime) implies
    invariant(s_prime) by {
        assert forall |msg| #[trigger] Self::in_flight_or_pending_req_message(s_prime, msg) implies (
        forall |other_msg: MsgType<E>| #[trigger] Self::in_flight_or_pending_req_message(s_prime, other_msg) && msg != other_msg
        ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()) by {
            assert forall |other_msg: MsgType<E>| #[trigger] Self::in_flight_or_pending_req_message(s_prime, other_msg) && msg != other_msg implies
            msg.content.get_rest_id() != other_msg.content.get_rest_id() by {
                let step = choose |step| Self::next_step(s, s_prime, step);
                if Self::in_flight_or_pending_req_message(s, other_msg) && Self::in_flight_or_pending_req_message(s, msg) {
                    assert(msg.content.get_rest_id() != other_msg.content.get_rest_id());
                } else if Self::in_flight_or_pending_req_message(s, msg) {
                    assert(msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter);
                } else if Self::in_flight_or_pending_req_message(s, other_msg) {
                    assert(other_msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter);
                }
            }
        }
    };
    init_invariant::<Self>(spec, Self::init(), stronger_next, invariant);
}

pub open spec fn every_in_flight_msg_has_unique_id() -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            #[trigger] s.message_in_flight(msg)
            ==> (
                forall |other_msg: MsgType<E>|
                    #[trigger] s.message_in_flight(other_msg)
                    && msg != other_msg
                    ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()
            )
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_unique_id(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(
            always(lift_state(Self::every_in_flight_msg_has_unique_id()))
        ),
{
    let invariant = Self::every_in_flight_msg_has_unique_id();
    let stronger_next = |s, s_prime: Self| {
        Self::next()(s, s_prime)
        && Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        && Self::every_in_flight_req_is_unique()(s)
    };
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    Self::lemma_always_every_in_flight_req_is_unique(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_req_is_unique())
    );
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime) implies
    invariant(s_prime) by {
        Self::next_and_unique_lower_msg_id_preserves_in_flight_msg_has_unique_id(s, s_prime);
    };
    init_invariant::<Self>(spec, Self::init(), stronger_next, invariant);
}

proof fn next_and_unique_lower_msg_id_preserves_in_flight_msg_has_unique_id(
    s: Self, s_prime: Self
)
    requires
        Self::next()(s, s_prime),
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Self::every_in_flight_req_is_unique()(s),
        Self::every_in_flight_msg_has_unique_id()(s), // the invariant
    ensures
        Self::every_in_flight_msg_has_unique_id()(s_prime),
{
    assert forall |msg: MsgType<E>| #[trigger] s_prime.message_in_flight(msg) implies
    (forall |other_msg: MsgType<E>| #[trigger] s_prime.message_in_flight(other_msg) && msg != other_msg
        ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()) by {
        assert forall |other_msg: MsgType<E>| #[trigger] s_prime.message_in_flight(other_msg) && msg != other_msg implies
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
    s: Self, s_prime: Self, msg_1: MsgType<E>, msg_2: MsgType<E>
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
        let next_step = choose |step: Step<MsgType<E>>| Self::next_step(s, s_prime, step);
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
    } else if msg_2.content.is_ExternalAPIResponse() {
        let next_step = choose |step: Step<MsgType<E>>| Self::next_step(s, s_prime, step);
        match next_step {
            Step::ExternalAPIStep(input) => {
                let req_msg = input.get_Some_0();
                assert(s.network_state.in_flight.count(req_msg) <= 1);
                assert(msg_1.content.get_rest_id() != msg_2.content.get_rest_id());
            }
            _ => assert(false),
        }
    }
}


pub open spec fn pending_req_has_lower_req_id_than_allocator() -> StatePred<Self> {
    |s: Self| {
        forall |cr_key: ObjectRef|
            #[trigger] s.reconcile_state_contains(cr_key)
            && Self::pending_k8s_api_req_msg(s, cr_key)
            ==> s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0().content.get_rest_id() < s.rest_id_allocator.rest_id_counter
    }
}

pub proof fn lemma_always_pending_req_has_lower_req_id_than_allocator(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::pending_req_has_lower_req_id_than_allocator()))),
{
    let invariant = Self::pending_req_has_lower_req_id_than_allocator();
    init_invariant::<Self>(
        spec, Self::init(), Self::next(), invariant
    );
}

}

}
