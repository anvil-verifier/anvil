// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, dynamic::*, resource::*};
use crate::kubernetes_cluster::spec::{
    api_server::types::ApiServerAction, builtin_controllers::types::*, cluster::*,
    cluster_state_machine::Step, message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vstd_ext::multiset_lib::*;
use vstd::assert_multisets_equal;
use vstd::prelude::*;

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub proof fn lemma_pre_leads_to_post_by_kubernetes_api(
    spec: TempPred<Self>, input: Option<MsgType<E>>, next: ActionPred<Self>, action: ApiServerAction<E::Input, E::Output>, pre: StatePred<Self>, post: StatePred<Self>
)
    requires
        Self::kubernetes_api().actions.contains(action),
        forall |s, s_prime: Self| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: Self| pre(s) && #[trigger] next(s, s_prime) && Self::kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: Self| #[trigger] pre(s) ==> Self::kubernetes_api_action_pre(action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
    ensures spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<Self, Option<MsgType<E>>>(spec, |i| Self::kubernetes_api_next().weak_fairness(i), input);
    Self::kubernetes_api_action_pre_implies_next_pre(action, input);
    entails_trans::<Self>(
        lift_state(pre),
        lift_state(Self::kubernetes_api_action_pre(action, input)),
        lift_state(Self::kubernetes_api_next().pre(input))
    );
    Self::kubernetes_api_next().wf1(input, spec, next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_by_builtin_controllers(
    spec: TempPred<Self>, input: (BuiltinControllerChoice, ObjectRef), next: ActionPred<Self>, action: BuiltinControllersAction<E::Input, E::Output>, pre: StatePred<Self>, post: StatePred<Self>
)
    requires
        Self::builtin_controllers().actions.contains(action),
        forall |s, s_prime: Self| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: Self| pre(s) && #[trigger] next(s, s_prime) && Self::builtin_controllers_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: Self| #[trigger] pre(s) ==> Self::builtin_controllers_action_pre(action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| Self::builtin_controllers_next().weak_fairness(i))),
    ensures spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<Self, (BuiltinControllerChoice, ObjectRef)>(spec, |i| Self::builtin_controllers_next().weak_fairness(i), input);
    Self::builtin_controllers_action_pre_implies_next_pre(action, input);
    entails_trans::<Self>(
        lift_state(pre),
        lift_state(Self::builtin_controllers_action_pre(action, input)),
        lift_state(Self::builtin_controllers_next().pre(input))
    );
    Self::builtin_controllers_next().wf1(input, spec, next, pre, post);
}

pub open spec fn no_req_before_rest_id_is_in_flight(rest_id: RestId) -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>| !{
            &&& #[trigger] s.in_flight().contains(msg)
            &&& api_request_msg_before(rest_id)(msg)
        }
    }
}

// To ensure that spec |= true ~> []every_in_fligh_message_satisfies(requirements), we only have to reason about the messages
// created after some points. Here, "requirements" takes two parameters, the new message and the prime state. In many cases,
// It's only related to the message.
//
// In detail, we have to show two things:
//     a. Newly created api request message satisfies requirements: s.in_flight(msg) /\ s_prime.in_flight(msg) ==> requirements(msg, s_prime).
//     b. The requirements, once satisfied, won't be violated as long as the message is still in flight:
//         s.in_flight(msg) /\ requirements(msg, s) /\ s_prime.in_flight(msg) ==> requirements(msg, s_prime).
//
// Previously, when "requirements" was irrelavant to the state, b will be sure to hold. Later, we find that "requirements" in some
// case does need some information in the state. So we add state as another parameter and requires the caller of the lemma
// lemma_true_leads_to_always_every_in_flight_req_msg_satisfies to prove b. is always satisfied. In order not to make those cases
// where "requirements" has nothing to do with state more difficult, we combine a. and b. together.
//
// Therefore, we have the following predicate. As is easy to see, this is similar as:
//     (s.in_flight(msg) ==> requirements(msg, s)) ==> (s_prime.in_flight(msg) ==> requirements(msg, s_prime))
// If we think of s.in_flight(msg) ==> requirements(msg, s) as an invariant, it is the same as the proof of invariants in previous
// proof strategy.
pub open spec fn every_new_req_msg_if_in_flight_then_satisfies(requirements: spec_fn(MsgType<E>, Self) -> bool) -> ActionPred<Self> {
    |s: Self, s_prime: Self| {
        forall |msg: MsgType<E>|
            {
                &&& (!s.in_flight().contains(msg) || requirements(msg, s))
                &&& #[trigger] s_prime.in_flight().contains(msg)
                &&& {
                    ||| msg.dst.is_ApiServer() && msg.content.is_APIRequest()
                    ||| msg.dst.is_ExternalAPI() && msg.content.is_ExternalAPIRequest()
                }
            } ==> requirements(msg, s_prime)
    }
}

pub open spec fn every_in_flight_req_msg_satisfies(requirements: spec_fn(MsgType<E>, Self) -> bool) -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            {
                &&& #[trigger] s.in_flight().contains(msg)
                &&& {
                    ||| msg.dst.is_ApiServer() && msg.content.is_APIRequest()
                    ||| msg.dst.is_ExternalAPI() && msg.content.is_ExternalAPIRequest()
                }
            } ==> requirements(msg, s)
    }
}

// This lemma shows that if spec ensures every newly created Kubernetes api request message satisfies some requirements,
// the system will eventually reaches a state where all Kubernetes api request messages satisfy those requirements.
//
// To require "every newly create Kubernetes api request message satisfies some requirements", we use a spec_fn (i.e., a closure)
// as parameter which can be defined by callers and require spec |= [](every_new_req_msg_if_in_flight_then_satisfies(requirements)).
//
// The last parameter must be equivalent to every_in_flight_req_msg_satisfies(requirements)
pub proof fn lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec: TempPred<Self>, requirements: spec_fn(MsgType<E>, Self) -> bool)
    requires
        spec.entails(always(lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))))),
{
    assert forall |rest_id| spec.entails(
        lift_state(#[trigger] Self::rest_id_counter_is(rest_id)).leads_to(always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))))
    ) by {
        Self::lemma_some_rest_id_leads_to_always_every_in_flight_req_msg_satisfies_with_rest_id(spec, requirements, rest_id);
    }
    let has_rest_id = |rest_id| lift_state(Self::rest_id_counter_is(rest_id));
    leads_to_exists_intro(spec, has_rest_id, always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))));
    assert_by(
        tla_exists(has_rest_id) == true_pred::<Self>(),
        {
            assert forall |ex| #[trigger] true_pred::<Self>().satisfied_by(ex)
            implies tla_exists(has_rest_id).satisfied_by(ex) by {
                let rest_id = ex.head().rest_id_allocator.rest_id_counter;
                assert(has_rest_id(rest_id).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(has_rest_id), true_pred::<Self>());
        }
    );
}

// This lemma is an assistant one for the previous one without rest_id.
pub proof fn lemma_some_rest_id_leads_to_always_every_in_flight_req_msg_satisfies_with_rest_id(spec: TempPred<Self>, requirements: spec_fn(MsgType<E>, Self) -> bool, rest_id: nat)
    requires
        spec.entails(always(lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
    ensures spec.entails(lift_state(Self::rest_id_counter_is(rest_id)).leads_to(always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))))),
{
    // Use the stable part of spec, show the stability of stable_spec and also spec |= stable_spec
    let always_spec = always(lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)))
                    .and(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator())))
                    .and(always(lift_action(Self::next())));
    let stable_spec = always_spec.and(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))).and(tla_forall(|i| Self::external_api_next().weak_fairness(i)));
    stable_and_always_n!(
        lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_action(Self::next())
    );
    Self::tla_forall_action_weak_fairness_is_stable(Self::kubernetes_api_next());
    Self::tla_forall_action_weak_fairness_is_stable(Self::external_api_next());
    stable_and_n!(always_spec, tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i)), tla_forall(|i| Self::external_api_next().weak_fairness(i)));
    entails_and_n!(
        spec,
        always(lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements))),
        always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator())),
        always(lift_action(Self::next())),
        tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i)),
        tla_forall(|i| Self::external_api_next().weak_fairness(i))
    );

    let spec_with_rest_id = stable_spec.and(lift_state(Self::rest_id_counter_is(rest_id)));

    eliminate_always(spec_with_rest_id, lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()));


    // With rest_id known, we first prove that spec /\ rest_id |= true ~> []every_in_flight_msg_is_expected
    // We divide the proof into three steps:
    // (1) Prove an invariant that forall message with a no smaller rest_id than rest_id, it satisfies the given predicate.
    // (2) Prove that spec |= true ~> []msg_has_lower_rest_id_all_gone.
    // (3) With the first invariant, prove that msg_has_lower_rest_id_all_gone implies all messages in flight are expected.
    assert_by(
        spec_with_rest_id.entails(true_pred().leads_to(always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))))),
        {
            Self::lemma_always_has_rest_id_counter_no_smaller_than(spec_with_rest_id, rest_id);
            let invariant = |s: Self| {
                forall |msg: MsgType<E>|
                {
                    &&& #[trigger] s.in_flight().contains(msg)
                    &&& msg.content.get_rest_id() >= rest_id
                    &&& {
                        ||| msg.dst.is_ApiServer() && msg.content.is_APIRequest()
                        ||| msg.dst.is_ExternalAPI() && msg.content.is_ExternalAPIRequest()
                    }
                } ==> requirements(msg, s)
            };
            assert_by(
                spec_with_rest_id.entails(always(lift_state(invariant))),
                {
                    let init = |s: Self| {
                        Self::rest_id_counter_is(rest_id)(s)
                        && Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
                    };
                    entails_and_temp(spec_with_rest_id, lift_state(Self::rest_id_counter_is(rest_id)), lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()));
                    temp_pred_equality(
                        lift_state(init), lift_state(Self::rest_id_counter_is(rest_id)).and(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))
                    );
                    let stronger_next = |s, s_prime| {
                        Self::next()(s, s_prime)
                        && Self::rest_id_counter_is_no_smaller_than(rest_id)(s)
                        && Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime)
                    };
                    combine_spec_entails_always_n!(
                        spec_with_rest_id, lift_action(stronger_next),
                        lift_action(Self::next()),
                        lift_state(Self::rest_id_counter_is_no_smaller_than(rest_id)),
                        lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements))
                    );
                    init_invariant(spec_with_rest_id, init, stronger_next, invariant);
                }
            );

            Self::lemma_true_leads_to_always_no_req_before_rest_id_is_in_flight(spec_with_rest_id, rest_id);

            entails_preserved_by_always(
                lift_state(invariant),
                lift_state(Self::no_req_before_rest_id_is_in_flight(rest_id))
                .implies(lift_state(Self::every_in_flight_req_msg_satisfies(requirements)))
            );
            entails_trans(
                spec_with_rest_id, always(lift_state(invariant)),
                always(lift_state(Self::no_req_before_rest_id_is_in_flight(rest_id)).implies(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))))
            );
            always_implies_preserved_by_always(spec_with_rest_id, lift_state(Self::no_req_before_rest_id_is_in_flight(rest_id)), lift_state(Self::every_in_flight_req_msg_satisfies(requirements)));
            leads_to_weaken(
                spec_with_rest_id,
                true_pred(), always(lift_state(Self::no_req_before_rest_id_is_in_flight(rest_id))),
                true_pred(), always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements)))
            );
        }
    );

    // Then unpack the condition from spec.
    unpack_conditions_from_spec(
        stable_spec, lift_state(Self::rest_id_counter_is(rest_id)), true_pred(),
        always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements)))
    );
    temp_pred_equality(true_pred().and(lift_state(Self::rest_id_counter_is(rest_id))), lift_state(Self::rest_id_counter_is(rest_id)));
    entails_trans(spec, stable_spec, lift_state(Self::rest_id_counter_is(rest_id)).leads_to(always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements)))));
}

// All the APIRequest messages with a smaller id than rest_id will eventually leave the network.
// The intuition is that (1) The number of such APIRequest messages are bounded by rest_id,
// and (2) weak fairness assumption ensures each message will eventually be handled by Kubernetes.
pub proof fn lemma_true_leads_to_always_no_req_before_rest_id_is_in_flight(spec: TempPred<Self>, rest_id: RestId)
    requires
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::rest_id_counter_is_no_smaller_than(rest_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::no_req_before_rest_id_is_in_flight(rest_id))))),
{
    Self::lemma_eventually_no_req_before_rest_id_is_in_flight(spec, rest_id);

    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& s.has_rest_id_counter_no_smaller_than(rest_id)
    };
    strengthen_next::<Self>(
        spec, Self::next(), Self::rest_id_counter_is_no_smaller_than(rest_id), stronger_next
    );

    assert forall |s, s_prime| Self::no_req_before_rest_id_is_in_flight(rest_id)(s) && #[trigger] stronger_next(s, s_prime)
    implies Self::no_req_before_rest_id_is_in_flight(rest_id)(s_prime) by {
        assert forall |msg| ! (#[trigger] s_prime.in_flight().contains(msg) && api_request_msg_before(rest_id)(msg)) by {
            if s.in_flight().contains(msg) {} else {}
        }
    }

    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(Self::no_req_before_rest_id_is_in_flight(rest_id)));
}

pub proof fn lemma_eventually_no_req_before_rest_id_is_in_flight(spec: TempPred<Self>, rest_id: RestId)
    requires
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::rest_id_counter_is_no_smaller_than(rest_id)))),
    ensures spec.entails(true_pred().leads_to(lift_state(Self::no_req_before_rest_id_is_in_flight(rest_id)))),
{
    let pending_requests_num_is_n = |msg_num: nat| lift_state(|s: Self| {
        s.network_state.in_flight.filter(api_request_msg_before(rest_id)).len() == msg_num
    });
    let no_more_pending_requests = lift_state(Self::no_req_before_rest_id_is_in_flight(rest_id));

    // Here we split the cases on the number of pending request messages
    // and prove that for all number, all the messages will eventually leave the network.
    assert forall |msg_num: nat|
        spec.entails(#[trigger] pending_requests_num_is_n(msg_num).leads_to(no_more_pending_requests))
    by {
        Self::lemma_pending_requests_number_is_n_leads_to_no_pending_requests(spec, rest_id, msg_num);
    }
    leads_to_exists_intro(spec, pending_requests_num_is_n, no_more_pending_requests);

    // Now we merge all the cases on different message number together to get true_pred().
    // We only need to prove tla_exists(pending_requests_num_is_n) == true_pred::<Self>(),
    // which is obvious.
    assert_by(tla_exists(pending_requests_num_is_n) == true_pred::<Self>(), {
        assert forall |ex| #[trigger] true_pred().satisfied_by(ex) implies
        tla_exists(pending_requests_num_is_n).satisfied_by(ex) by {
            let current_msg_num = ex.head().network_state.in_flight.filter(api_request_msg_before(rest_id)).len();
            assert(pending_requests_num_is_n(current_msg_num).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pending_requests_num_is_n), true_pred());
    });
}

// This is an inductive proof to show that if there are msg_num requests with id lower than rest_id in the network,
// then eventually all of them will be gone.
proof fn lemma_pending_requests_number_is_n_leads_to_no_pending_requests(spec: TempPred<Self>, rest_id: RestId, msg_num: nat)
    requires
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::rest_id_counter_is_no_smaller_than(rest_id)))),
    ensures spec.entails(lift_state(|s: Self| {s.network_state.in_flight.filter(api_request_msg_before(rest_id)).len() == msg_num}).leads_to(lift_state(Self::no_req_before_rest_id_is_in_flight(rest_id)))),
    decreases msg_num
{
    if msg_num == 0 {
        // The base case:
        // If there are 0 such requests, then all of them are gone.
        let pending_requests_num_is_zero = |s: Self| {
            s.network_state.in_flight.filter(api_request_msg_before(rest_id)).len() == 0
        };
        let no_more_pending_requests = Self::no_req_before_rest_id_is_in_flight(rest_id);

        assert_by(valid(lift_state(pending_requests_num_is_zero).implies(lift_state(no_more_pending_requests))), {
            assert forall |s: Self| #[trigger] pending_requests_num_is_zero(s) implies no_more_pending_requests(s) by {
                assert forall |msg| api_request_msg_before(rest_id)(msg) implies !s.in_flight().contains(msg) by {
                    assert(s.in_flight().filter(api_request_msg_before(rest_id)).count(msg) == 0);
                }
            }
        });
        entails_implies_leads_to(spec, lift_state(pending_requests_num_is_zero), lift_state(no_more_pending_requests));
    } else {
        // The induction step:
        // If we already have "there are msg_num-1 such requests" ~> "all such requests are gone" (the inductive hypothesis),
        // then we only need to prove "there are msg_num such requests" ~> "there are msg_num-1 such requests",
        // which seems to be just one wf1 away.
        let pending_requests_num_is_msg_num = lift_state(|s: Self| {
            s.network_state.in_flight.filter(api_request_msg_before(rest_id)).len() == msg_num
        });
        let pending_requests_num_is_msg_num_minus_1 = lift_state(|s: Self| {
            s.network_state.in_flight.filter(api_request_msg_before(rest_id)).len() == (msg_num - 1) as nat
        });
        let no_more_pending_requests = lift_state(Self::no_req_before_rest_id_is_in_flight(rest_id));
        let pending_req_in_flight = |msg: MsgType<E>| lift_state(|s: Self| {
            s.network_state.in_flight.filter(api_request_msg_before(rest_id)).count(msg) > 0
        });
        let pending_requests_num_is_msg_num_and_pending_req_in_flight = |msg: MsgType<E>| lift_state(|s: Self| {
            &&& s.network_state.in_flight.filter(api_request_msg_before(rest_id)).len() == msg_num
            &&& s.network_state.in_flight.filter(api_request_msg_before(rest_id)).count(msg) > 0
        });
        // But to apply wf1 to get "there are msg_num such requests" ~> "there are msg_num-1 such requests",
        // we need a concrete message to serve as the input of the forward action.
        // So here we split cases on different request messages in the network so that we have a concrete message
        // to reason about.
        assert forall |msg: MsgType<E>| spec.entails(
            #[trigger] pending_requests_num_is_msg_num_and_pending_req_in_flight(msg)
                .leads_to(pending_requests_num_is_msg_num_minus_1)
        ) by {
            Self::pending_requests_num_decreases(spec, rest_id, msg_num, msg);
        }
        leads_to_exists_intro(
            spec, pending_requests_num_is_msg_num_and_pending_req_in_flight, pending_requests_num_is_msg_num_minus_1
        );
        // Now we merge all the splitted cases on different concrete messages.
        assert_by(tla_exists(pending_requests_num_is_msg_num_and_pending_req_in_flight) == pending_requests_num_is_msg_num, {
            assert forall |ex| #[trigger] pending_requests_num_is_msg_num.satisfied_by(ex)
            implies tla_exists(pending_requests_num_is_msg_num_and_pending_req_in_flight).satisfied_by(ex) by {
                let msg = ex.head().network_state.in_flight.filter(api_request_msg_before(rest_id)).choose();
//                assert(ex.head().network_state.in_flight.filter(api_request_msg_before(rest_id)).count(msg) > 0);
                assert(pending_requests_num_is_msg_num_and_pending_req_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(
                tla_exists(pending_requests_num_is_msg_num_and_pending_req_in_flight), pending_requests_num_is_msg_num
            );
        });
        // We use the inductive hypothesis here.
        Self::lemma_pending_requests_number_is_n_leads_to_no_pending_requests(
            spec, rest_id, (msg_num - 1) as nat
        );
        leads_to_trans(
            spec, pending_requests_num_is_msg_num, pending_requests_num_is_msg_num_minus_1, no_more_pending_requests
        );
    }
}

// TODO: broken by pod_event; Xudong will fix it later
#[verifier(external_body)]
proof fn pending_requests_num_decreases(spec: TempPred<Self>, rest_id: RestId, msg_num: nat, msg: MsgType<E>)
    requires
        msg_num > 0,
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::rest_id_counter_is_no_smaller_than(rest_id)))),
    ensures
        spec.entails(lift_state(|s: Self| {
                &&& s.network_state.in_flight.filter(api_request_msg_before(rest_id)).len() == msg_num
                &&& s.network_state.in_flight.filter(api_request_msg_before(rest_id)).count(msg) > 0
            }).leads_to(lift_state(|s: Self| {
                    s.network_state.in_flight.filter(api_request_msg_before(rest_id)).len() == (msg_num - 1) as nat
            }))),
{
    let pre = |s: Self| {
        &&& s.network_state.in_flight.filter(api_request_msg_before(rest_id)).len() == msg_num
        &&& s.network_state.in_flight.filter(api_request_msg_before(rest_id)).count(msg) > 0
    };
    let post = |s: Self| {
        s.network_state.in_flight.filter(api_request_msg_before(rest_id)).len() == (msg_num - 1) as nat
    };
    let input = Some(msg);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& s.has_rest_id_counter_no_smaller_than(rest_id)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::rest_id_counter_is_no_smaller_than(rest_id))
    );

//    assert forall |s, s_prime: Self| pre(s) && #[trigger] stronger_next(s, s_prime)
//    implies pre(s_prime) || post(s_prime) by {
//        let pending_req_multiset = s.network_state.in_flight.filter(api_request_msg_before(rest_id));
//        let pending_req_multiset_prime = s_prime.network_state.in_flight.filter(api_request_msg_before(rest_id));
//        let step = choose |step| Self::next_step(s, s_prime, step);
//        match step {
//            Step::ApiServerStep(input) => {
//                if pending_req_multiset.count(input.get_Some_0()) > 0 {
////                    assert(pending_req_multiset.remove(input.get_Some_0()) =~= pending_req_multiset_prime);
//                } else {
////                    assert(pending_req_multiset =~= pending_req_multiset_prime);
//                }
//            },
//            Step::FailTransientlyStep(input) => {
//                if pending_req_multiset.count(input.0) > 0 {
////                    assert(pending_req_multiset.remove(input.0) =~= pending_req_multiset_prime);
//                } else {
////                    assert(pending_req_multiset =~= pending_req_multiset_prime);
//                }
//            },
//            Step::BuiltinControllersStep(input) => {
////                assert(pending_req_multiset =~= pending_req_multiset_prime);
//            },
//            Step::ControllerStep(input) => {
////                assert(pending_req_multiset =~= pending_req_multiset_prime);
//            },
//            Step::ClientStep() => {
////                assert(pending_req_multiset =~= pending_req_multiset_prime);
//            },
//            Step::ExternalAPIStep(input) => {
//                if pending_req_multiset.count(input.get_Some_0()) > 0 {
////                    assert(pending_req_multiset.remove(input.get_Some_0()) =~= pending_req_multiset_prime);
//                } else {
////                    assert(pending_req_multiset =~= pending_req_multiset_prime);
//                }
//            },
//            _ => {}
//        }
//    }

    if msg.dst.is_ApiServer() {
//        assert forall |s, s_prime: Self|
//            pre(s) && #[trigger] stronger_next(s, s_prime) && Self::kubernetes_api_next().forward(input)(s, s_prime)
//        implies post(s_prime) by {
//            let pending_req_multiset = s.network_state.in_flight.filter(api_request_msg_before(rest_id));
//            let pending_req_multiset_prime = s_prime.network_state.in_flight.filter(api_request_msg_before(rest_id));
////            assert(pending_req_multiset.remove(msg) =~= pending_req_multiset_prime);
//        }
        Self::lemma_pre_leads_to_post_by_kubernetes_api(
            spec, input, stronger_next, Self::handle_request(), pre, post
        );
    } else {
//        assert forall |s, s_prime: Self|
//            pre(s) && #[trigger] stronger_next(s, s_prime) && Self::external_api_next().forward(input)(s, s_prime)
//        implies post(s_prime) by {
//            let pending_req_multiset = s.network_state.in_flight.filter(api_request_msg_before(rest_id));
//            let pending_req_multiset_prime = s_prime.network_state.in_flight.filter(api_request_msg_before(rest_id));
////            assert(pending_req_multiset.remove(msg) =~= pending_req_multiset_prime);
//        }
        Self::lemma_pre_leads_to_post_by_external_api(
            spec, input, stronger_next, Self::handle_external_request(), pre, post
        );
    }
}

}

}