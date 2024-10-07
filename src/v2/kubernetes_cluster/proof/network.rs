use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::transition_by_etcd, cluster::*, message::*,
};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn rpc_id_counter_is(rpc_id: nat) -> StatePred<ClusterState> {
    |s: ClusterState| s.rpc_id_allocator.rpc_id_counter == rpc_id
}

pub open spec fn rpc_id_counter_is_no_smaller_than(rpc_id: nat) -> StatePred<ClusterState> {
    |s: ClusterState| s.rpc_id_allocator.rpc_id_counter >= rpc_id
}

pub proof fn lemma_always_has_rpc_id_counter_no_smaller_than(
    self, spec: TempPred<ClusterState>, rpc_id: RPCId
)
    requires
        spec.entails(lift_state(Self::rpc_id_counter_is(rpc_id))),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::rpc_id_counter_is_no_smaller_than(rpc_id)))),
{
    let invariant = Self::rpc_id_counter_is_no_smaller_than(rpc_id);
    init_invariant::<ClusterState>(spec, Self::rpc_id_counter_is(rpc_id), self.next(), invariant);
}

pub open spec fn every_in_flight_msg_has_lower_id_than_allocator() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg)
            ==> msg.rpc_id < s.rpc_id_allocator.rpc_id_counter
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_lower_id_than_allocator(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
{
    let invariant = Self::every_in_flight_msg_has_lower_id_than_allocator();
    assert forall |s, s_prime| invariant(s) && #[trigger] self.next()(s, s_prime) implies invariant(s_prime) by {
        assert forall |msg: Message| #[trigger] s_prime.in_flight().contains(msg) implies
        msg.rpc_id < s_prime.rpc_id_allocator.rpc_id_counter by {
            let step = choose |step| self.next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                assert(s.rpc_id_allocator.rpc_id_counter <= s_prime.rpc_id_allocator.rpc_id_counter);
            } else {
                match step {
                    Step::ControllerStep(_) => {},
                    Step::APIServerStep(input) => {
                        assert(s.in_flight().contains(input.get_Some_0()));
                        assert(msg.rpc_id == input.get_Some_0().rpc_id);
                    },
                    Step::DropReqStep(input) => {
                        assert(s.in_flight().contains(input.0));
                        assert(msg.rpc_id == input.0.rpc_id);
                    },
                    Step::ExternalStep(_) => {},
                    _ => {},
                }
            }
        }
    };
    init_invariant::<ClusterState>(spec, self.init(), self.next(), invariant);
}

pub open spec fn every_pending_req_msg_has_lower_id_than_allocator(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            && s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
            ==> s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().rpc_id < s.rpc_id_allocator.rpc_id_counter
    }
}

pub proof fn lemma_always_every_pending_req_msg_has_lower_id_than_allocator(self, spec: TempPred<ClusterState>, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::every_pending_req_msg_has_lower_id_than_allocator(controller_id)))),
{
    let invariant = Self::every_pending_req_msg_has_lower_id_than_allocator(controller_id);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    let next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(self.next()), lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant::<ClusterState>(spec, self.init(), next, invariant);
}

pub open spec fn pending_req_of_key_is_unique_with_unique_id(controller_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.ongoing_reconciles(controller_id).contains_key(key)
        && s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
        ==> (
            forall |other_key: ObjectRef|
                #[trigger] s.ongoing_reconciles(controller_id).contains_key(other_key)
                && key != other_key
                && s.ongoing_reconciles(controller_id)[other_key].pending_req_msg.is_Some()
                ==> s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().rpc_id
                    != s.ongoing_reconciles(controller_id)[other_key].pending_req_msg.get_Some_0().rpc_id
        )
    }
}

pub proof fn lemma_always_pending_req_of_key_is_unique_with_unique_id(self, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))),
{
    let inv = Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key);
    let next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::every_pending_req_msg_has_lower_id_than_allocator(controller_id)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    self.lemma_always_every_pending_req_msg_has_lower_id_than_allocator(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(self.next()), lift_state(Self::every_pending_req_msg_has_lower_id_than_allocator(controller_id)), lift_state(Self::there_is_the_controller_state(controller_id))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) && s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some() {
            assert forall |other_key: ObjectRef|
            #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(other_key) && s_prime.ongoing_reconciles(controller_id)[other_key].pending_req_msg.is_Some() && key != other_key
            implies
                s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().rpc_id != s_prime.ongoing_reconciles(controller_id)[other_key].pending_req_msg.get_Some_0().rpc_id
            by {
                let step = choose |step| self.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        let input_controller_id = input.0;
                        let input_key = input.2.get_Some_0();
                        if input_controller_id == controller_id {
                            if input_key == key {
                                assert(s.ongoing_reconciles(controller_id).contains_key(other_key) && s.ongoing_reconciles(controller_id)[other_key].pending_req_msg.is_Some());
                                assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().rpc_id == s.rpc_id_allocator.rpc_id_counter);
                            } else {
                                assert(s.ongoing_reconciles(controller_id).contains_key(key) && s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some());
                                if s_prime.ongoing_reconciles(controller_id).contains_key(input_key) && s_prime.ongoing_reconciles(controller_id)[input_key].pending_req_msg.is_Some() {
                                    assert(s.ongoing_reconciles(controller_id).contains_key(input_key));
                                    assert(s_prime.ongoing_reconciles(controller_id)[input_key].pending_req_msg.get_Some_0().rpc_id == s.rpc_id_allocator.rpc_id_counter);
                                }
                            }
                        }
                    },
                    _ => {}
                }
            }
        }
    }
    init_invariant(spec, self.init(), next, inv);
}

pub open spec fn every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let pending_req = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
        s.ongoing_reconciles(controller_id).contains_key(key)
        && s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
        ==> {
            forall |msg: Message|
                #[trigger] s.in_flight().contains(msg)
                && msg.content.is_APIRequest()
                && msg != pending_req
                ==> msg.rpc_id != pending_req.rpc_id
        }

    }
}

pub proof fn lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(self, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, key)))),
{
    let invariant = Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, key);
    let stronger_next = |s, s_prime| {
        self.next()(s, s_prime)
        && Self::there_is_the_controller_state(controller_id)(s)
        && Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        && Self::every_pending_req_msg_has_lower_id_than_allocator(controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    self.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    self.lemma_always_every_pending_req_msg_has_lower_id_than_allocator(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id)),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_pending_req_msg_has_lower_id_than_allocator(controller_id))
    );
    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) && s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some() {
            let pending_req = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
            assert forall |msg: Message|
                #[trigger] s_prime.in_flight().contains(msg) && msg.content.is_APIRequest() && msg != pending_req
            implies
                msg.rpc_id != pending_req.rpc_id
            by {
                let step = choose |step| self.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        let input_controller_id = input.0;
                        let input_key = input.2.get_Some_0();
                        if input_controller_id == controller_id {
                            if input_key == key {
                                assert(pending_req.rpc_id == s.rpc_id_allocator.rpc_id_counter);
                                if s.in_flight().contains(msg) {} else {}
                                assert(msg.rpc_id < s.rpc_id_allocator.rpc_id_counter);
                            } else {
                                assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                                assert(pending_req.rpc_id < s.rpc_id_allocator.rpc_id_counter);
                                if s.in_flight().contains(msg) {} else {}
                            }
                        } else {
                            assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                            assert(pending_req.rpc_id < s.rpc_id_allocator.rpc_id_counter);
                            if s.in_flight().contains(msg) {} else {}
                        }
                    },
                    _ => {
                        assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                        if !s.in_flight().contains(msg) {
                            assert(pending_req.rpc_id < s.rpc_id_allocator.rpc_id_counter);
                            assert(msg.rpc_id == s.rpc_id_allocator.rpc_id_counter)
                        }
                    }
                }
            }
        }
    };
    init_invariant::<ClusterState>(spec, self.init(), stronger_next, invariant);
}

pub open spec fn every_in_flight_msg_has_no_replicas_and_has_unique_id() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg|
            #[trigger] s.in_flight().contains(msg)
            ==> s.in_flight().count(msg) == 1
                && (
                    forall |other_msg|
                        #[trigger] s.in_flight().contains(other_msg)
                        && msg != other_msg
                        ==> msg.rpc_id != other_msg.rpc_id
                )
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_no_replicas_and_has_unique_id(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::every_in_flight_msg_has_no_replicas_and_has_unique_id()))),
{
    let invariant = Self::every_in_flight_msg_has_no_replicas_and_has_unique_id();
    let stronger_next = |s, s_prime| {
        self.next()(s, s_prime)
        && Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    self.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator())
    );
    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |msg: Message| #[trigger] s_prime.in_flight().contains(msg)
        implies
            s_prime.in_flight().count(msg) == 1
            && (forall |other_msg: Message| #[trigger] s_prime.in_flight().contains(other_msg) && msg != other_msg
                ==> msg.rpc_id != other_msg.rpc_id)
        by {
            let step = choose |step| self.next_step(s, s_prime, step);
            assert_by(
                s_prime.in_flight().count(msg) == 1, {
                    match step {
                        Step::APIServerStep(input) => {
                            let req = input.get_Some_0();
                            let (_, resp) = transition_by_etcd(self.installed_types, req, s.api_server);
                            assert(resp.rpc_id == req.rpc_id);
                            assert(s.in_flight().contains(req));
                            if s.in_flight().contains(msg) {
                                assert(s.in_flight().count(msg) == 1);
                                assert(msg.rpc_id != resp.rpc_id);
                                assert(s_prime.in_flight().count(msg) == 1);
                            } else {
                                assert(msg == resp);
                                assert(s_prime.in_flight().count(resp) == 1);
                            }
                        },
                        Step::DropReqStep(input) => {
                            let req = input.0;
                            assert(s.in_flight().contains(req));
                            if s.in_flight().contains(msg) {
                                assert(s.in_flight().count(msg) == 1);
                                assert(s_prime.in_flight().count(msg) == 1);
                            } else {
                                assert(s_prime.in_flight().count(msg) == 1);
                            }
                        },
                        _ => {
                            if s.in_flight().contains(msg) {
                                assert(s.in_flight().count(msg) == 1);
                            }
                        },
                    }
                }
            );
            assert forall |other_msg: Message| #[trigger] s_prime.in_flight().contains(other_msg) && msg != other_msg implies
            msg.rpc_id != other_msg.rpc_id by {
                // At most one message will be added to the network_state.in_flight for each action.
                assert(s.in_flight().contains(msg) || s.in_flight().contains(other_msg));
                if s.in_flight().contains(msg) && s.in_flight().contains(other_msg) {
                    assert(msg.rpc_id != other_msg.rpc_id);
                } else {
                    if (s.in_flight().contains(msg)) {
                        self.newly_added_msg_have_different_id_from_existing_ones(s, s_prime, msg, other_msg);
                    } else {
                        self.newly_added_msg_have_different_id_from_existing_ones(s, s_prime, other_msg, msg);
                    }
                }
            }
        }
    };
    init_invariant::<ClusterState>(spec, self.init(), stronger_next, invariant);
}

proof fn newly_added_msg_have_different_id_from_existing_ones(self, s: ClusterState, s_prime: ClusterState, msg_1: Message, msg_2: Message)
    requires
        self.next()(s, s_prime),
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s),
        s.in_flight().contains(msg_1),
        !s.in_flight().contains(msg_2),
        s_prime.in_flight().contains(msg_1),
        s_prime.in_flight().contains(msg_2),
        Self::every_in_flight_msg_has_no_replicas_and_has_unique_id()(s), // the invariant
    ensures msg_1.rpc_id != msg_2.rpc_id,
{
    if msg_2.content.is_APIResponse() {
        let next_step = choose |step| self.next_step(s, s_prime, step);
        match next_step {
            Step::APIServerStep(input) => {
                let req_msg = input.get_Some_0();
                assert(s.network.in_flight.count(req_msg) <= 1);
                assert(msg_1.rpc_id != msg_2.rpc_id);
            }
            Step::DropReqStep(input) => {
                let req_msg = input.0;
                assert(s.network.in_flight.count(req_msg) <= 1);
                assert(msg_1.rpc_id != msg_2.rpc_id);
            }
            _ => assert(false),
        }
    } else if msg_2.content.is_ExternalResponse() {
        let next_step = choose |step| self.next_step(s, s_prime, step);
        match next_step {
            Step::ExternalStep(input) => {
                let req_msg = input.1.get_Some_0();
                assert(s.network.in_flight.count(req_msg) <= 1);
                assert(msg_1.rpc_id != msg_2.rpc_id);
            }
            _ => assert(false),
        }
    }
}

pub open spec fn every_in_flight_msg_has_unique_id() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg1, msg2|
            #[trigger] s.in_flight().contains(msg1)
            && #[trigger] s.in_flight().contains(msg2)
            && msg1 != msg2
            ==>  msg1.rpc_id != msg2.rpc_id
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_unique_id(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
{
    self.lemma_always_every_in_flight_msg_has_no_replicas_and_has_unique_id(spec);
    assert forall |s| #[trigger] Self::every_in_flight_msg_has_no_replicas_and_has_unique_id()(s) implies Self::every_in_flight_msg_has_unique_id()(s) by {
        assert forall |msg1, msg2| #[trigger] s.in_flight().contains(msg1) && #[trigger] s.in_flight().contains(msg2) && msg1 != msg2
        implies msg1.rpc_id != msg2.rpc_id by {}
    };
    always_weaken::<ClusterState>(spec, lift_state(Self::every_in_flight_msg_has_no_replicas_and_has_unique_id()), lift_state(Self::every_in_flight_msg_has_unique_id()));
}

}

}
