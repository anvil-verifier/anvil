// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, error::*, resource::*};
use crate::kubernetes_cluster::{
    proof::{
        controller_runtime::*, kubernetes_api_safety,
        wf1_assistant::controller_action_pre_implies_next_pre,
    },
    spec::{
        cluster::*,
        controller::common::{ControllerAction, ControllerActionInput},
        controller::state_machine::controller,
        kubernetes_api::state_machine::{handle_request, transition_by_etcd},
        message::*,
    },
};
use crate::reconciler::spec::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

pub open spec fn every_in_flight_msg_has_lower_id_than_allocator<K: ResourceView, T>() -> StatePred<State<K, T>> {
    |s: State<K, T>| {
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            ==> msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_lower_id_than_allocator
    <K: ResourceView, T, ReconcilerType: Reconciler<K, T>>()
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(always(lift_state(every_in_flight_msg_has_lower_id_than_allocator()))),
{
    let invariant = every_in_flight_msg_has_lower_id_than_allocator::<K, T>();
    assert forall |s, s_prime: State<K, T>| invariant(s) && #[trigger] next::<K, T, ReconcilerType>()(s, s_prime) implies
    invariant(s_prime) by {
        next_preserves_every_in_flight_msg_has_lower_id_than_allocator::<K, T, ReconcilerType>(s, s_prime);
    };
    init_invariant::<State<K, T>>(sm_spec::<K, T, ReconcilerType>(), init::<K, T, ReconcilerType>(), next::<K, T, ReconcilerType>(), invariant);
}

proof fn next_preserves_every_in_flight_msg_has_lower_id_than_allocator<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    s: State<K, T>, s_prime: State<K, T>
)
    requires
        every_in_flight_msg_has_lower_id_than_allocator::<K, T>()(s), next::<K, T, ReconcilerType>()(s, s_prime),
    ensures
        every_in_flight_msg_has_lower_id_than_allocator::<K, T>()(s_prime),
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
                    let next_step = choose |step: Step<K>| next_step::<K, T, ReconcilerType>(s, s_prime, step);
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

pub open spec fn every_in_flight_req_is_unique<K: ResourceView, T>() -> StatePred<State<K, T>> {
    |s: State<K, T>| {
        forall |msg: Message|
            msg.content.is_APIRequest() && #[trigger] s.message_in_flight(msg)
            ==> s.network_state.in_flight.count(msg) == 1
    }
}

pub proof fn lemma_always_every_in_flight_req_is_unique<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>()
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(
            always(lift_state(every_in_flight_req_is_unique::<K, T>()))
        ),
{
    let invariant = every_in_flight_req_is_unique::<K, T>();
    let stronger_next = |s, s_prime: State<K, T>| {
        &&& next::<K, T, ReconcilerType>()(s, s_prime)
        &&& every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    lemma_always_every_in_flight_msg_has_lower_id_than_allocator::<K, T, ReconcilerType>();
    strengthen_next::<State<K, T>>(
        sm_spec::<K, T, ReconcilerType>(), next::<K, T, ReconcilerType>(), every_in_flight_msg_has_lower_id_than_allocator(), stronger_next
    );
    assert forall |s, s_prime: State<K, T>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies
    invariant(s_prime) by {
        assert forall |msg: Message| msg.content.is_APIRequest() && #[trigger] s_prime.message_in_flight(msg) implies
        s_prime.network_state.in_flight.count(msg) == 1 by {
            if (s.message_in_flight(msg)) {
                assert(s.network_state.in_flight.count(msg) == 1);
            }
        };
    };
    init_invariant::<State<K, T>>(sm_spec::<K, T, ReconcilerType>(), init::<K, T, ReconcilerType>(), stronger_next, invariant);
}

pub open spec fn every_in_flight_msg_has_unique_id<K: ResourceView, T>() -> StatePred<State<K, T>> {
    |s: State<K, T>| {
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

pub proof fn lemma_always_every_in_flight_msg_has_unique_id<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>()
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(
            always(lift_state(every_in_flight_msg_has_unique_id::<K, T>()))
        ),
{
    let invariant = every_in_flight_msg_has_unique_id::<K, T>();
    let stronger_next = |s, s_prime: State<K, T>| {
        next::<K, T, ReconcilerType>()(s, s_prime)
        && every_in_flight_msg_has_lower_id_than_allocator::<K, T>()(s)
        && every_in_flight_req_is_unique::<K, T>()(s)
    };
    lemma_always_every_in_flight_msg_has_lower_id_than_allocator::<K, T, ReconcilerType>();
    lemma_always_every_in_flight_req_is_unique::<K, T, ReconcilerType>();
    entails_always_and_n!(
        sm_spec::<K, T, ReconcilerType>(),
        lift_action(next::<K, T, ReconcilerType>()),
        lift_state(every_in_flight_msg_has_lower_id_than_allocator::<K, T>()),
        lift_state(every_in_flight_req_is_unique::<K, T>())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<K, T, ReconcilerType>())
            .and(lift_state(every_in_flight_msg_has_lower_id_than_allocator::<K, T>()))
            .and(lift_state(every_in_flight_req_is_unique::<K, T>()))
    );
    assert forall |s, s_prime: State<K, T>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies
    invariant(s_prime) by {
        next_and_unique_lower_msg_id_preserves_in_flight_msg_has_unique_id::<K, T, ReconcilerType>(s, s_prime);
    };
    init_invariant::<State<K, T>>(sm_spec::<K, T, ReconcilerType>(), init::<K, T, ReconcilerType>(), stronger_next, invariant);
}

proof fn next_and_unique_lower_msg_id_preserves_in_flight_msg_has_unique_id<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    s: State<K, T>, s_prime: State<K, T>
)
    requires
        next::<K, T, ReconcilerType>()(s, s_prime),
        every_in_flight_msg_has_lower_id_than_allocator::<K, T>()(s),
        every_in_flight_req_is_unique::<K, T>()(s),
        every_in_flight_msg_has_unique_id::<K, T>()(s), // the invariant
    ensures
        every_in_flight_msg_has_unique_id::<K, T>()(s_prime),
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
                    newly_added_msg_have_different_id_from_existing_ones::<K, T, ReconcilerType>(s, s_prime, msg, other_msg);
                } else {
                    newly_added_msg_have_different_id_from_existing_ones::<K, T, ReconcilerType>(s, s_prime, other_msg, msg);
                }
            }
        }
    };
}

proof fn newly_added_msg_have_different_id_from_existing_ones<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    s: State<K, T>, s_prime: State<K, T>, msg_1: Message, msg_2: Message
)
    requires
        next::<K, T, ReconcilerType>()(s, s_prime),
        every_in_flight_msg_has_lower_id_than_allocator::<K, T>()(s),
        every_in_flight_req_is_unique::<K, T>()(s),
        s.message_in_flight(msg_1),
        !s.message_in_flight(msg_2),
        s_prime.message_in_flight(msg_1),
        s_prime.message_in_flight(msg_2),
        every_in_flight_msg_has_unique_id::<K, T>()(s), // the invariant
    ensures
        msg_1.content.get_rest_id() != msg_2.content.get_rest_id(),
{
    if (msg_2.content.is_APIResponse()) {
        let next_step = choose |step: Step<K>| next_step::<K, T, ReconcilerType>(s, s_prime, step);
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

pub open spec fn req_in_flight_or_pending_at_controller<K: ResourceView, T>(req_msg: Message, s: State<K, T>) -> bool {
    req_msg.content.is_APIRequest() && (s.message_in_flight(req_msg)
    || exists |cr_key: ObjectRef| (
        #[trigger] s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).pending_req_msg == Option::Some(req_msg)
    ))
}

pub open spec fn every_in_flight_or_pending_req_has_unique_id<K: ResourceView, T>() -> StatePred<State<K, T>> {
    |s: State<K, T>| {
        forall |msg1, msg2: Message|
            #![trigger req_in_flight_or_pending_at_controller(msg1, s), req_in_flight_or_pending_at_controller(msg2, s)]
            req_in_flight_or_pending_at_controller(msg1, s)
            && req_in_flight_or_pending_at_controller(msg2, s)
            && msg1 != msg2
            ==> msg1.content.get_req_id() != msg2.content.get_req_id()
    }
}

pub proof fn lemma_always_every_in_flight_or_pending_req_has_unique_id<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>()
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(
            always(lift_state(every_in_flight_or_pending_req_has_unique_id::<K, T>()))
        ),
{
    let invariant = every_in_flight_or_pending_req_has_unique_id::<K, T>();
    let stronger_next = |s, s_prime: State<K, T>| {
        next::<K, T, ReconcilerType>()(s, s_prime)
        && every_in_flight_msg_has_lower_id_than_allocator::<K, T>()(s)
        && pending_req_has_lower_req_id_than_allocator::<K, T>()(s)
    };
    lemma_always_every_in_flight_msg_has_lower_id_than_allocator::<K, T, ReconcilerType>();
    lemma_always_pending_req_has_lower_req_id_than_allocator::<K, T, ReconcilerType>();
    entails_always_and_n!(
        sm_spec::<K, T, ReconcilerType>(),
        lift_action(next::<K, T, ReconcilerType>()),
        lift_state(every_in_flight_msg_has_lower_id_than_allocator::<K, T>()),
        lift_state(pending_req_has_lower_req_id_than_allocator::<K, T>())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<K, T, ReconcilerType>())
            .and(lift_state(every_in_flight_msg_has_lower_id_than_allocator::<K, T>()))
            .and(lift_state(pending_req_has_lower_req_id_than_allocator::<K, T>()))
    );
    assert forall |s, s_prime: State<K, T>| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |req_msg, other_msg: Message| #[trigger] req_in_flight_or_pending_at_controller(req_msg, s_prime)
        && #[trigger] req_in_flight_or_pending_at_controller(other_msg, s_prime) && req_msg != other_msg
        implies req_msg.content.get_req_id() != other_msg.content.get_req_id() by {
            if req_in_flight_or_pending_at_controller(req_msg, s) && req_in_flight_or_pending_at_controller(other_msg, s) {
                assert(req_msg.content.get_req_id() != other_msg.content.get_req_id());
            } else if req_in_flight_or_pending_at_controller(req_msg, s) {
                assert(req_msg.content.get_req_id() != other_msg.content.get_req_id());
            } else if req_in_flight_or_pending_at_controller(other_msg, s) {
                assert(req_msg.content.get_req_id() != other_msg.content.get_req_id());
            }
        };
    };
    init_invariant::<State<K, T>>(sm_spec::<K, T, ReconcilerType>(), init::<K, T, ReconcilerType>(), stronger_next, invariant);
}

pub open spec fn pending_req_has_lower_req_id_than_allocator<K: ResourceView, T>() -> StatePred<State<K, T>> {
    |s: State<K, T>| {
        forall |cr_key: ObjectRef|
            #[trigger] s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
            ==> s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0().content.get_req_id() < s.rest_id_allocator.rest_id_counter
    }
}

pub proof fn lemma_always_pending_req_has_lower_req_id_than_allocator<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>()
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(always(lift_state(pending_req_has_lower_req_id_than_allocator()))),
{
    let invariant = pending_req_has_lower_req_id_than_allocator::<K, T>();
    init_invariant::<State<K, T>>(
        sm_spec::<K, T, ReconcilerType>(), init::<K, T, ReconcilerType>(), next::<K, T, ReconcilerType>(), invariant
    );
}

pub open spec fn resp_matches_at_most_one_pending_req<K: ResourceView, T>(
    resp_msg: Message, cr_key: ObjectRef
) -> StatePred<State<K, T>> {
    |s: State<K, T>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
        && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
        ==> (
            forall |other_key: ObjectRef|
                #[trigger] s.reconcile_state_contains(other_key)
                && s.reconcile_state_of(other_key).pending_req_msg.is_Some()
                && other_key != cr_key
                ==> !resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(other_key).pending_req_msg.get_Some_0())
            )
    }
}

pub open spec fn resp_if_matches_pending_req_then_no_other_resp_matches<K: ResourceView, T>(
    resp_msg: Message, cr_key: ObjectRef
) -> StatePred<State<K, T>> {
    |s: State<K, T>| {
        s.reconcile_state_contains(cr_key)
        && s.message_in_flight(resp_msg)
        && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
        && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
        ==> (
            forall |other_resp: Message| other_resp != resp_msg && #[trigger] s.message_in_flight(other_resp)
            ==> !resp_msg_matches_req_msg(other_resp, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
        )
    }
}

pub proof fn lemma_always_resp_if_matches_pending_req_then_no_other_resp_matches<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    resp_msg: Message, cr_key: ObjectRef
)
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(
            always(lift_state(resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key)))
        ),
{
    implies_preserved_by_always::<State<K, T>>(
        every_in_flight_msg_has_unique_id::<K, T>(), resp_if_matches_pending_req_then_no_other_resp_matches::<K, T>(resp_msg, cr_key)
    );
    lemma_always_every_in_flight_msg_has_unique_id::<K, T, ReconcilerType>();
    entails_trans::<State<K, T>>(
        sm_spec::<K, T, ReconcilerType>(),
        always(lift_state(every_in_flight_msg_has_unique_id::<K, T>())),
        always(lift_state(resp_if_matches_pending_req_then_no_other_resp_matches::<K, T>(resp_msg, cr_key)))
    );
}

pub proof fn lemma_forall_always_resp_if_matches_pending_req_then_no_other_resp_matches<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    cr_key: ObjectRef
)
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(
            tla_forall(|resp_msg: Message| always(lift_state(resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key))))
        ),
{
    let m_to_p = |msg| always(lift_state(resp_if_matches_pending_req_then_no_other_resp_matches(msg, cr_key)));
    assert forall |msg| #[trigger] sm_spec::<K, T, ReconcilerType>().entails(m_to_p(msg)) by {
        lemma_always_resp_if_matches_pending_req_then_no_other_resp_matches::<K, T, ReconcilerType>(msg, cr_key);
    }
    spec_entails_tla_forall(sm_spec::<K, T, ReconcilerType>(), m_to_p);
}

pub open spec fn each_resp_if_matches_pending_req_then_no_other_resp_matches<K: ResourceView, T>(
    cr_key: ObjectRef
) -> StatePred<State<K, T>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<K, T>| {
        forall |resp_msg: Message|
            s.reconcile_state_contains(cr_key)
            && #[trigger] s.message_in_flight(resp_msg)
            && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
            && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
            ==> (
                forall |other_resp: Message| other_resp != resp_msg && #[trigger] s.message_in_flight(other_resp)
                ==> !resp_msg_matches_req_msg(other_resp, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
            )
    }
}

pub proof fn lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(
            always(lift_state(each_resp_if_matches_pending_req_then_no_other_resp_matches(cr_key)))
        ),
{
    let spec = sm_spec::<K, T, ReconcilerType>();
    let forall_a_to_p = lift_state(each_resp_if_matches_pending_req_then_no_other_resp_matches(cr_key));
    let a_to_p = |resp_msg: Message| lift_state(resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key));
    let a_to_always_p = |resp_msg: Message| always(a_to_p(resp_msg));
    assert forall |resp_msg: Message| spec.entails(#[trigger] a_to_always_p(resp_msg))
    by {
        lemma_always_resp_if_matches_pending_req_then_no_other_resp_matches::<K, T, ReconcilerType>(resp_msg, cr_key);
    }
    spec_entails_tla_forall(spec, a_to_always_p);
    tla_forall_always_equality(a_to_p);

    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies forall_a_to_p.satisfied_by(ex) by {
        assert forall |resp_msg: Message|
            ex.head().reconcile_state_contains(cr_key)
            && #[trigger] ex.head().message_in_flight(resp_msg)
            && ex.head().reconcile_state_of(cr_key).pending_req_msg.is_Some()
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

pub proof fn lemma_always_resp_matches_at_most_one_pending_req<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    resp_msg: Message, cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(always(lift_state(resp_matches_at_most_one_pending_req(resp_msg, cr_key)))),
{
    let invariant = resp_matches_at_most_one_pending_req::<K, T>(resp_msg, cr_key);
    let stronger_next = |s, s_prime: State<K, T>| {
        &&& next::<K, T, ReconcilerType>()(s, s_prime)
        &&& pending_req_has_lower_req_id_than_allocator()(s)
    };

    lemma_always_pending_req_has_lower_req_id_than_allocator::<K, T, ReconcilerType>();

    strengthen_next::<State<K, T>>(
        sm_spec::<K, T, ReconcilerType>(), next::<K, T, ReconcilerType>(), pending_req_has_lower_req_id_than_allocator(), stronger_next
    );
    init_invariant::<State<K, T>>(sm_spec::<K, T, ReconcilerType>(), init::<K, T, ReconcilerType>(), stronger_next, invariant);
}

pub proof fn lemma_forall_resp_always_matches_at_most_one_pending_req<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(
            tla_forall(|msg| always(lift_state(resp_matches_at_most_one_pending_req(msg, cr_key))))
        ),
{
    let m_to_p = |msg| always(lift_state(resp_matches_at_most_one_pending_req(msg, cr_key)));
    assert forall |msg| #[trigger] sm_spec::<K, T, ReconcilerType>().entails(m_to_p(msg)) by {
        lemma_always_resp_matches_at_most_one_pending_req::<K, T, ReconcilerType>(msg, cr_key);
    };
    spec_entails_tla_forall(sm_spec::<K, T, ReconcilerType>(), m_to_p);
}

pub open spec fn each_resp_matches_at_most_one_pending_req<K: ResourceView, T>(
    cr_key: ObjectRef
) -> StatePred<State<K, T>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<K, T>| {
        forall |resp_msg: Message|
            s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).pending_req_msg.is_Some()
            && #[trigger] resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr_key).pending_req_msg.get_Some_0())
            ==> (
                forall |other_key: ObjectRef|
                    #[trigger] s.reconcile_state_contains(other_key)
                    && s.reconcile_state_of(other_key).pending_req_msg.is_Some()
                    && other_key != cr_key
                    ==> !resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(other_key).pending_req_msg.get_Some_0())
                )
    }
}

pub proof fn lemma_always_each_resp_matches_at_most_one_pending_req<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec::<K, T, ReconcilerType>().entails(always(lift_state(each_resp_matches_at_most_one_pending_req(cr_key)))),
{
    let invariant = each_resp_matches_at_most_one_pending_req::<K, T>(cr_key);
    let stronger_next = |s, s_prime: State<K, T>| {
        &&& next::<K, T, ReconcilerType>()(s, s_prime)
        &&& pending_req_has_lower_req_id_than_allocator()(s)
    };

    lemma_always_pending_req_has_lower_req_id_than_allocator::<K, T, ReconcilerType>();

    strengthen_next::<State<K, T>>(
        sm_spec::<K, T, ReconcilerType>(), next::<K, T, ReconcilerType>(),
        pending_req_has_lower_req_id_than_allocator(), stronger_next
    );
    init_invariant::<State<K, T>>(sm_spec::<K, T, ReconcilerType>(), init::<K, T, ReconcilerType>(), stronger_next, invariant);
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
pub proof fn lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, key: ObjectRef, state: T
)
    requires
        state != ReconcilerType::reconcile_init_state(),
        forall |cr: K, resp_o: Option<APIResponse>, pre_state: T| #[trigger] ReconcilerType::reconcile_core(cr, resp_o, pre_state).0 == state
            ==> ReconcilerType::reconcile_core(cr, resp_o, pre_state).1.is_Some(),
        spec.entails(lift_state(init::<K, T, ReconcilerType>())),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(always(lift_state(each_resp_matches_at_most_one_pending_req::<K, T>(key)))),
    ensures
        spec.entails(
            always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state(key, state)))
        ),
{
    let invariant = pending_req_in_flight_or_resp_in_flight_at_reconcile_state(key, state);
    let stronger_next = |s, s_prime: State<K ,T>| {
        &&& next::<K, T, ReconcilerType>()(s, s_prime)
        &&& each_resp_matches_at_most_one_pending_req::<K, T>(key)(s)
    };
    assert forall |s, s_prime: State<K, T>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        if at_reconcile_state(key, state)(s_prime) {
            let next_step = choose |step| next_step::<K, T, ReconcilerType>(s, s_prime, step);
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
                    let cr_key = input.1.get_Some_0();
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
    strengthen_next::<State<K, T>>(spec, next::<K, T, ReconcilerType>(), each_resp_matches_at_most_one_pending_req::<K, T>(key), stronger_next);
    init_invariant::<State<K, T>>(spec, init::<K, T, ReconcilerType>(), stronger_next, invariant);
}

pub proof fn lemma_always_no_pending_req_at_reconcile_init_state<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, key: ObjectRef
)
    requires
        spec.entails(lift_state(init::<K, T, ReconcilerType>())),
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        forall |cr: K, resp_o: Option<APIResponse>, pre_state: T|
            #[trigger] ReconcilerType::reconcile_core(cr, resp_o, pre_state).0 == ReconcilerType::reconcile_init_state()
            ==> ReconcilerType::reconcile_core(cr, resp_o, pre_state).1.is_None(),
    ensures
        spec.entails(always(lift_state(no_pending_req_at_reconcile_init_state::<K, T, ReconcilerType>(key)))),
{
    let invariant = no_pending_req_at_reconcile_init_state::<K, T, ReconcilerType>(key);
    assert forall |s, s_prime: State<K, T>| invariant(s) &&
    #[trigger] next::<K, T, ReconcilerType>()(s, s_prime) implies invariant(s_prime) by {
        if at_reconcile_state(key, ReconcilerType::reconcile_init_state())(s_prime) {
            if s.controller_state == s_prime.controller_state {
                assert(s.reconcile_state_of(key).pending_req_msg.is_None());
                assert(s_prime.reconcile_state_of(key).pending_req_msg.is_None());
            } else {
                assert(s_prime.reconcile_state_of(key).pending_req_msg.is_None());
            }
        }
    }
    init_invariant(spec, init::<K, T, ReconcilerType>(), next::<K, T, ReconcilerType>(), invariant);
}

}
