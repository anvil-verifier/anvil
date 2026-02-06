use crate::kubernetes_cluster::spec::{api_server::types::*, cluster::*, message::*};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn no_req_before_rpc_id_is_in_flight(rpc_id: RPCId) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| !{
            &&& #[trigger] s.in_flight().contains(msg)
            &&& api_request_msg_before(rpc_id)(msg)
        }
    }
}

// similar to no_pending_request_to_api_server_from_api_server_or_external,
// but forbids messages from PodMonkey
pub open spec fn no_pending_request_to_api_server_from_non_controllers() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| !{
            &&& #[trigger] s.in_flight().contains(msg)
            &&& !(msg.src is Controller || msg.src is BuiltinController)
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        }
    }
}

pub proof fn lemma_true_leads_to_always_no_pending_request_to_api_server_from_non_controllers(
    self, spec: TempPred<ClusterState>
)
    requires
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::no_pending_request_to_api_server_from_non_controllers())))),
{
    let requirements = |msg: Message, s: ClusterState| !{
        &&& !(msg.src is Controller || msg.src is BuiltinController)
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
    };
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(self.next()),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled())
    );
    self.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(Self::no_pending_request_to_api_server_from_non_controllers()),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}


// To ensure that spec |= true ~> []every_in_flight_message_satisfies(requirements), we only have to reason about the messages
// created after some points. Here, "requirements" takes two parameters, the new message and the prime state. In many cases,
// It's only related to the message.
//
// In detail, we have to show two things:
//      a. Newly created api request message satisfies requirements:
//          !s.in_flight(msg) /\ s_prime.in_flight(msg) ==> requirements(msg, s_prime).
//      b. The requirements, once satisfied, won't be violated as long as the message is still in flight:
//          s.in_flight(msg) /\ requirements(msg, s) /\ s_prime.in_flight(msg) ==> requirements(msg, s_prime).
//
// Previously, when "requirements" was irrelevant to the state, b will be sure to hold. Later, we find that "requirements" in some
// case does need some information in the state. So we add state as another parameter and requires the caller of the lemma
// lemma_true_leads_to_always_every_in_flight_req_msg_satisfies to prove b. is always satisfied. In order not to make those cases
// where "requirements" has nothing to do with state more difficult, we combine a. and b. together.
//
// Therefore, we have the following predicate. As is easy to see, this is similar as:
//     (s.in_flight(msg) ==> requirements(msg, s)) ==> (s_prime.in_flight(msg) ==> requirements(msg, s_prime))
// If we think of s.in_flight(msg) ==> requirements(msg, s) as an invariant, it is the same as the proof of invariants in previous
// proof strategy.
pub open spec fn every_new_req_msg_if_in_flight_then_satisfies(requirements: spec_fn(Message, ClusterState) -> bool) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        forall |msg: Message|
            {
                &&& (!s.in_flight().contains(msg) || requirements(msg, s))
                &&& #[trigger] s_prime.in_flight().contains(msg)
                &&& msg.dst is APIServer && msg.content is APIRequest
            } ==> requirements(msg, s_prime)
    }
}

pub open spec fn every_in_flight_req_msg_satisfies(requirements: spec_fn(Message, ClusterState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            {
                &&& #[trigger] s.in_flight().contains(msg)
                &&& msg.dst is APIServer && msg.content is APIRequest
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
pub proof fn lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(self, spec: TempPred<ClusterState>, requirements: spec_fn(Message, ClusterState) -> bool)
    requires
        spec.entails(always(lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))))),
{
    assert forall |rpc_id| spec.entails(
        lift_state(#[trigger] Self::rpc_id_counter_is(rpc_id)).leads_to(always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))))
    ) by {
        self.lemma_some_rpc_id_leads_to_always_every_in_flight_req_msg_satisfies_with_rpc_id(spec, requirements, rpc_id);
    }
    let has_rpc_id = |rpc_id| lift_state(Self::rpc_id_counter_is(rpc_id));
    leads_to_exists_intro(spec, has_rpc_id, always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))));
    assert_by(
        tla_exists(has_rpc_id) == true_pred::<ClusterState>(),
        {
            assert forall |ex| #[trigger] true_pred::<ClusterState>().satisfied_by(ex)
            implies tla_exists(has_rpc_id).satisfied_by(ex) by {
                let rpc_id = ex.head().rpc_id_allocator.rpc_id_counter;
                assert(has_rpc_id(rpc_id).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(has_rpc_id), true_pred::<ClusterState>());
        }
    );
}

// This lemma is an assistant one for the previous one without rpc_id.
pub proof fn lemma_some_rpc_id_leads_to_always_every_in_flight_req_msg_satisfies_with_rpc_id(self, spec: TempPred<ClusterState>, requirements: spec_fn(Message, ClusterState) -> bool, rpc_id: nat)
    requires
        spec.entails(always(lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
    ensures spec.entails(lift_state(Self::rpc_id_counter_is(rpc_id)).leads_to(always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))))),
{
    // Use the stable part of spec, show the stability of stable_spec and also spec |= stable_spec
    let always_spec = always(lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)))
                    .and(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator())))
                    .and(always(lift_action(self.next())));
    let stable_spec = always_spec.and(tla_forall(|i| self.api_server_next().weak_fairness(i)));
    stable_and_always_n!(
        lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_action(self.next())
    );
    Self::tla_forall_action_weak_fairness_is_stable(self.api_server_next());
    stable_and_n!(always_spec, tla_forall(|i| self.api_server_next().weak_fairness(i)));
    entails_and_n!(
        spec,
        always(lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements))),
        always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator())),
        always(lift_action(self.next())),
        tla_forall(|i| self.api_server_next().weak_fairness(i))
    );

    let spec_with_rpc_id = stable_spec.and(lift_state(Self::rpc_id_counter_is(rpc_id)));

    eliminate_always(spec_with_rpc_id, lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()));


    // With rpc_id known, we first prove that spec /\ rpc_id |= true ~> []every_in_flight_msg_is_expected
    // We divide the proof into three steps:
    // (1) Prove an invariant that forall message with a no smaller rpc_id than rpc_id, it satisfies the given predicate.
    // (2) Prove that spec |= true ~> []msg_has_lower_rpc_id_all_gone.
    // (3) With the first invariant, prove that msg_has_lower_rpc_id_all_gone implies all messages in flight are expected.
    assert_by(
        spec_with_rpc_id.entails(true_pred().leads_to(always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))))),
        {
            self.lemma_always_has_rpc_id_counter_no_smaller_than(spec_with_rpc_id, rpc_id);
            let invariant = |s: ClusterState| {
                forall |msg: Message|
                {
                    &&& #[trigger] s.in_flight().contains(msg)
                    &&& msg.rpc_id >= rpc_id
                    &&& msg.dst is APIServer && msg.content is APIRequest
                } ==> requirements(msg, s)
            };
            assert_by(
                spec_with_rpc_id.entails(always(lift_state(invariant))),
                {
                    let init = |s: ClusterState| {
                        Self::rpc_id_counter_is(rpc_id)(s)
                        && Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
                    };
                    entails_and_temp(spec_with_rpc_id, lift_state(Self::rpc_id_counter_is(rpc_id)), lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()));
                    temp_pred_equality(
                        lift_state(init), lift_state(Self::rpc_id_counter_is(rpc_id)).and(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))
                    );
                    let stronger_next = |s, s_prime| {
                        self.next()(s, s_prime)
                        && Self::rpc_id_counter_is_no_smaller_than(rpc_id)(s)
                        && Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime)
                    };
                    combine_spec_entails_always_n!(
                        spec_with_rpc_id, lift_action(stronger_next),
                        lift_action(self.next()),
                        lift_state(Self::rpc_id_counter_is_no_smaller_than(rpc_id)),
                        lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements))
                    );
                    init_invariant(spec_with_rpc_id, init, stronger_next, invariant);
                }
            );

            self.lemma_true_leads_to_always_no_req_before_rpc_id_is_in_flight(spec_with_rpc_id, rpc_id);

            entails_preserved_by_always(
                lift_state(invariant),
                lift_state(Self::no_req_before_rpc_id_is_in_flight(rpc_id))
                .implies(lift_state(Self::every_in_flight_req_msg_satisfies(requirements)))
            );
            entails_trans(
                spec_with_rpc_id, always(lift_state(invariant)),
                always(lift_state(Self::no_req_before_rpc_id_is_in_flight(rpc_id)).implies(lift_state(Self::every_in_flight_req_msg_satisfies(requirements))))
            );
            always_implies_preserved_by_always(spec_with_rpc_id, lift_state(Self::no_req_before_rpc_id_is_in_flight(rpc_id)), lift_state(Self::every_in_flight_req_msg_satisfies(requirements)));
            leads_to_weaken(
                spec_with_rpc_id,
                true_pred(), always(lift_state(Self::no_req_before_rpc_id_is_in_flight(rpc_id))),
                true_pred(), always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements)))
            );
        }
    );

    // Then unpack the condition from spec.
    unpack_conditions_from_spec(
        stable_spec, lift_state(Self::rpc_id_counter_is(rpc_id)), true_pred(),
        always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements)))
    );
    temp_pred_equality(true_pred().and(lift_state(Self::rpc_id_counter_is(rpc_id))), lift_state(Self::rpc_id_counter_is(rpc_id)));
    entails_trans(spec, stable_spec, lift_state(Self::rpc_id_counter_is(rpc_id)).leads_to(always(lift_state(Self::every_in_flight_req_msg_satisfies(requirements)))));
}

// All the APIRequest messages with a smaller id than rpc_id will eventually leave the network.
// The intuition is that (1) The number of such APIRequest messages are bounded by rpc_id,
// and (2) weak fairness assumption ensures each message will eventually be handled by Kubernetes.
pub proof fn lemma_true_leads_to_always_no_req_before_rpc_id_is_in_flight(self, spec: TempPred<ClusterState>, rpc_id: RPCId)
    requires
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::rpc_id_counter_is_no_smaller_than(rpc_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::no_req_before_rpc_id_is_in_flight(rpc_id))))),
{
    self.lemma_eventually_no_req_before_rpc_id_is_in_flight(spec, rpc_id);

    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& s.has_rpc_id_counter_no_smaller_than(rpc_id)
    };
    strengthen_next::<ClusterState>(
        spec, self.next(), Self::rpc_id_counter_is_no_smaller_than(rpc_id), stronger_next
    );

    assert forall |s, s_prime| Self::no_req_before_rpc_id_is_in_flight(rpc_id)(s) && #[trigger] stronger_next(s, s_prime)
    implies Self::no_req_before_rpc_id_is_in_flight(rpc_id)(s_prime) by {
        assert forall |msg| ! (#[trigger] s_prime.in_flight().contains(msg) && api_request_msg_before(rpc_id)(msg)) by {
            if s.in_flight().contains(msg) {} else {}
        }
    }

    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(Self::no_req_before_rpc_id_is_in_flight(rpc_id)));
}

pub proof fn lemma_eventually_no_req_before_rpc_id_is_in_flight(self, spec: TempPred<ClusterState>, rpc_id: RPCId)
    requires
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::rpc_id_counter_is_no_smaller_than(rpc_id)))),
    ensures spec.entails(true_pred().leads_to(lift_state(Self::no_req_before_rpc_id_is_in_flight(rpc_id)))),
{
    let pending_requests_num_is_n = |msg_num: nat| lift_state(|s: ClusterState| {
        s.network.in_flight.filter(api_request_msg_before(rpc_id)).len() == msg_num
    });
    let no_more_pending_requests = lift_state(Self::no_req_before_rpc_id_is_in_flight(rpc_id));

    // Here we split the cases on the number of pending request messages
    // and prove that for all number, all the messages will eventually leave the network.
    assert forall |msg_num: nat|
        spec.entails(#[trigger] pending_requests_num_is_n(msg_num).leads_to(no_more_pending_requests))
    by {
        self.lemma_pending_requests_number_is_n_leads_to_no_pending_requests(spec, rpc_id, msg_num);
    }
    leads_to_exists_intro(spec, pending_requests_num_is_n, no_more_pending_requests);

    // Now we merge all the cases on different message number together to get true_pred().
    // We only need to prove tla_exists(pending_requests_num_is_n) == true_pred::<ClusterState>(),
    // which is obvious.
    assert_by(tla_exists(pending_requests_num_is_n) == true_pred::<ClusterState>(), {
        assert forall |ex| #[trigger] true_pred().satisfied_by(ex) implies
        tla_exists(pending_requests_num_is_n).satisfied_by(ex) by {
            let current_msg_num = ex.head().network.in_flight.filter(api_request_msg_before(rpc_id)).len();
            assert(pending_requests_num_is_n(current_msg_num).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pending_requests_num_is_n), true_pred());
    });
}

// This is an inductive proof to show that if there are msg_num requests with id lower than rpc_id in the network,
// then eventually all of them will be gone.
proof fn lemma_pending_requests_number_is_n_leads_to_no_pending_requests(self, spec: TempPred<ClusterState>, rpc_id: RPCId, msg_num: nat)
    requires
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::rpc_id_counter_is_no_smaller_than(rpc_id)))),
    ensures
        spec.entails(lift_state(|s: ClusterState| s.network.in_flight.filter(api_request_msg_before(rpc_id)).len() == msg_num).leads_to(lift_state(Self::no_req_before_rpc_id_is_in_flight(rpc_id)))),
    decreases msg_num
{
    if msg_num == 0 {
        // The base case:
        // If there are 0 such requests, then all of them are gone.
        let pending_requests_num_is_zero = |s: ClusterState| {
            s.network.in_flight.filter(api_request_msg_before(rpc_id)).len() == 0
        };
        let no_more_pending_requests = Self::no_req_before_rpc_id_is_in_flight(rpc_id);

        assert_by(valid(lift_state(pending_requests_num_is_zero).implies(lift_state(no_more_pending_requests))), {
            assert forall |s| #[trigger] pending_requests_num_is_zero(s) implies no_more_pending_requests(s) by {
                assert forall |msg| api_request_msg_before(rpc_id)(msg) implies !s.in_flight().contains(msg) by {
                    assert(s.in_flight().filter(api_request_msg_before(rpc_id)).count(msg) == 0);
                }
            }
        });
        entails_implies_leads_to(spec, lift_state(pending_requests_num_is_zero), lift_state(no_more_pending_requests));
    } else {
        // The induction step:
        // If we already have "there are msg_num-1 such requests" ~> "all such requests are gone" (the inductive hypothesis),
        // then we only need to prove "there are msg_num such requests" ~> "there are msg_num-1 such requests",
        // which seems to be just one wf1 away.
        let pending_requests_num_is_msg_num = lift_state(|s: ClusterState| {
            s.network.in_flight.filter(api_request_msg_before(rpc_id)).len() == msg_num
        });
        let pending_requests_num_is_msg_num_minus_1 = lift_state(|s: ClusterState| {
            s.network.in_flight.filter(api_request_msg_before(rpc_id)).len() == (msg_num - 1) as nat
        });
        let no_more_pending_requests = lift_state(Self::no_req_before_rpc_id_is_in_flight(rpc_id));
        let pending_req_in_flight = |msg: Message| lift_state(|s: ClusterState| {
            s.network.in_flight.filter(api_request_msg_before(rpc_id)).count(msg) > 0
        });
        let pending_requests_num_is_msg_num_and_pending_req_in_flight = |msg: Message| lift_state(|s: ClusterState| {
            &&& s.network.in_flight.filter(api_request_msg_before(rpc_id)).len() == msg_num
            &&& s.network.in_flight.filter(api_request_msg_before(rpc_id)).count(msg) > 0
        });
        // But to apply wf1 to get "there are msg_num such requests" ~> "there are msg_num-1 such requests",
        // we need a concrete message to serve as the input of the forward action.
        // So here we split cases on different request messages in the network so that we have a concrete message
        // to reason about.
        assert forall |msg: Message| spec.entails(
            #[trigger] pending_requests_num_is_msg_num_and_pending_req_in_flight(msg)
                .leads_to(pending_requests_num_is_msg_num_minus_1)
        ) by {
            self.pending_requests_num_decreases(spec, rpc_id, msg_num, msg);
        }
        leads_to_exists_intro(
            spec, pending_requests_num_is_msg_num_and_pending_req_in_flight, pending_requests_num_is_msg_num_minus_1
        );
        // Now we merge all the splitted cases on different concrete messages.
        assert_by(tla_exists(pending_requests_num_is_msg_num_and_pending_req_in_flight) == pending_requests_num_is_msg_num, {
            assert forall |ex| #[trigger] pending_requests_num_is_msg_num.satisfied_by(ex)
            implies tla_exists(pending_requests_num_is_msg_num_and_pending_req_in_flight).satisfied_by(ex) by {
                let msg = ex.head().network.in_flight.filter(api_request_msg_before(rpc_id)).choose();
                assert(ex.head().network.in_flight.filter(api_request_msg_before(rpc_id)).count(msg) > 0);
                assert(pending_requests_num_is_msg_num_and_pending_req_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(
                tla_exists(pending_requests_num_is_msg_num_and_pending_req_in_flight), pending_requests_num_is_msg_num
            );
        });
        // We use the inductive hypothesis here.
        self.lemma_pending_requests_number_is_n_leads_to_no_pending_requests(
            spec, rpc_id, (msg_num - 1) as nat
        );
        leads_to_trans(
            spec, pending_requests_num_is_msg_num, pending_requests_num_is_msg_num_minus_1, no_more_pending_requests
        );
    }
}

proof fn pending_requests_num_decreases(self, spec: TempPred<ClusterState>, rpc_id: RPCId, msg_num: nat, msg: Message)
    requires
        msg_num > 0,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::rpc_id_counter_is_no_smaller_than(rpc_id)))),
    ensures
        spec.entails(lift_state(|s: ClusterState| {
                &&& s.network.in_flight.filter(api_request_msg_before(rpc_id)).len() == msg_num
                &&& s.network.in_flight.filter(api_request_msg_before(rpc_id)).count(msg) > 0
            }).leads_to(lift_state(|s: ClusterState| {
                s.network.in_flight.filter(api_request_msg_before(rpc_id)).len() == (msg_num - 1) as nat
            }))),
{
    let pre = |s: ClusterState| {
        &&& s.network.in_flight.filter(api_request_msg_before(rpc_id)).len() == msg_num
        &&& s.network.in_flight.filter(api_request_msg_before(rpc_id)).count(msg) > 0
    };
    let post = |s: ClusterState| {
        s.network.in_flight.filter(api_request_msg_before(rpc_id)).len() == (msg_num - 1) as nat
    };
    let input = Some(msg);
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& s.has_rpc_id_counter_no_smaller_than(rpc_id)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::rpc_id_counter_is_no_smaller_than(rpc_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime)
    implies pre(s_prime) || post(s_prime) by {
        let pending_req_multiset = s.network.in_flight.filter(api_request_msg_before(rpc_id));
        let pending_req_multiset_prime = s_prime.network.in_flight.filter(api_request_msg_before(rpc_id));
        let step = choose |step| self.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                if pending_req_multiset.count(input->0) > 0 {
                    assert(pending_req_multiset.remove(input->0) =~= pending_req_multiset_prime);
                } else {
                    assert(pending_req_multiset =~= pending_req_multiset_prime);
                }
            },
            Step::DropReqStep(input) => {
                if pending_req_multiset.count(input.0) > 0 {
                    assert(pending_req_multiset.remove(input.0) =~= pending_req_multiset_prime);
                } else {
                    assert(pending_req_multiset =~= pending_req_multiset_prime);
                }
            },
            Step::BuiltinControllersStep(input) => {
                assert(pending_req_multiset =~= pending_req_multiset_prime);
            },
            Step::ControllerStep(input) => {
                assert(pending_req_multiset =~= pending_req_multiset_prime);
            },
            Step::PodMonkeyStep(input) => {
                assert(pending_req_multiset =~= pending_req_multiset_prime);
            },
            Step::ExternalStep(input) => {
                assert(pending_req_multiset =~= pending_req_multiset_prime);
            },
            _ => {}
        }
    }

    if msg.dst is APIServer {
        assert forall |s, s_prime|
            pre(s) && #[trigger] stronger_next(s, s_prime) && self.api_server_next().forward(input)(s, s_prime)
        implies post(s_prime) by {
            let pending_req_multiset = s.network.in_flight.filter(api_request_msg_before(rpc_id));
            let pending_req_multiset_prime = s_prime.network.in_flight.filter(api_request_msg_before(rpc_id));
            assert(pending_req_multiset.remove(msg) =~= pending_req_multiset_prime);
        }
        self.lemma_pre_leads_to_post_by_api_server(
            spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
        );
    }
}

}

}
