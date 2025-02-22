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

pub open spec fn every_in_flight_msg_has_lower_id_than_allocator() -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            #[trigger] s.in_flight().contains(msg)
            ==> msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
{
    let invariant = Self::every_in_flight_msg_has_lower_id_than_allocator();
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] Self::next()(s, s_prime) implies invariant(s_prime) by {
        assert forall |msg: MsgType<E>| #[trigger] s_prime.in_flight().contains(msg) implies
        msg.content.get_rest_id() < s_prime.rest_id_allocator.rest_id_counter by {
            let id = msg.content.get_rest_id();
            let step = choose |step| Self::next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
//                assert(s.rest_id_allocator.rest_id_counter <= s_prime.rest_id_allocator.rest_id_counter);
            } else {
                match step {
                    Step::ControllerStep(_) => {},
                    Step::ApiServerStep(input) => {
//                        assert(s.in_flight().contains(input.get_Some_0()));
//                        assert(id == input.get_Some_0().content.get_rest_id());
                    },
                    Step::FailTransientlyStep(input) => {
//                        assert(s.in_flight().contains(input.0));
//                        assert(id == input.0.content.get_rest_id());
                    },
                    Step::ExternalAPIStep(_) => {},
                    _ => {},
                }
            }
        }
    };
    init_invariant::<Self>(spec, Self::init(), Self::next(), invariant);
}

pub open spec fn every_pending_req_msg_has_lower_id_than_allocator() -> StatePred<Self> {
    |s: Self| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles().contains_key(key)
            && s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            ==> s.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_rest_id() < s.rest_id_allocator.rest_id_counter
    }
}

pub proof fn lemma_always_every_pending_req_msg_has_lower_id_than_allocator(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::every_pending_req_msg_has_lower_id_than_allocator()))),
{
    let invariant = Self::every_pending_req_msg_has_lower_id_than_allocator();
    init_invariant::<Self>(spec, Self::init(), Self::next(), invariant);
}

pub open spec fn pending_req_of_key_is_unique_with_unique_id(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        s.ongoing_reconciles().contains_key(key)
        && s.ongoing_reconciles()[key].pending_req_msg.is_Some()
        ==> (
            forall |other_key: ObjectRef|
                #[trigger] s.ongoing_reconciles().contains_key(other_key)
                && key != other_key
                && s.ongoing_reconciles()[other_key].pending_req_msg.is_Some()
                ==> s.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_rest_id()
                    != s.ongoing_reconciles()[other_key].pending_req_msg.get_Some_0().content.get_rest_id()
        )
    }
}

pub proof fn lemma_always_pending_req_of_key_is_unique_with_unique_id(spec: TempPred<Self>, key: ObjectRef)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(key)))),
{
    let inv = Self::pending_req_of_key_is_unique_with_unique_id(key);
    let next = |s: Self, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::every_pending_req_msg_has_lower_id_than_allocator()(s)
    };
    Self::lemma_always_every_pending_req_msg_has_lower_id_than_allocator(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(Self::next()), lift_state(Self::every_pending_req_msg_has_lower_id_than_allocator())
    );
//    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
//        if s_prime.ongoing_reconciles().contains_key(key) && s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some() {
////            assert forall |other_key: ObjectRef|
////            #[trigger] s_prime.ongoing_reconciles().contains_key(other_key) && s_prime.ongoing_reconciles()[other_key].pending_req_msg.is_Some()
////            && key != other_key implies s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_rest_id()
////            != s_prime.ongoing_reconciles()[other_key].pending_req_msg.get_Some_0().content.get_rest_id() by {
////                let step = choose |step| Self::next_step(s, s_prime, step);
////                match step {
////                    Step::ControllerStep(input) => {
////                        let cr_key = input.1.get_Some_0();
////                        if cr_key == key {
//////                            assert(s.ongoing_reconciles().contains_key(other_key) && s.ongoing_reconciles()[other_key].pending_req_msg.is_Some());
//////                            assert(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_rest_id() == s.rest_id_allocator.rest_id_counter);
////                        } else {
//////                            assert(s.ongoing_reconciles().contains_key(key) && s.ongoing_reconciles()[key].pending_req_msg.is_Some());
////                            if s_prime.ongoing_reconciles().contains_key(cr_key) && s_prime.ongoing_reconciles()[cr_key].pending_req_msg.is_Some() {
//////                                assert(s.ongoing_reconciles().contains_key(cr_key));
//////                                assert(s_prime.ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0().content.get_rest_id() == s.rest_id_allocator.rest_id_counter);
////                            }
////                        }
////                    },
////                    _ => {}
////                }
////            }
//        }
//    }
    init_invariant(spec, Self::init(), next, inv);
}

pub open spec fn every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        let pending_req = s.ongoing_reconciles()[key].pending_req_msg.get_Some_0();
        s.ongoing_reconciles().contains_key(key)
        && s.ongoing_reconciles()[key].pending_req_msg.is_Some()
        ==> {
            forall |msg: MsgType<E>|
                #[trigger] s.in_flight().contains(msg)
                && msg.content.is_APIRequest()
                && msg != pending_req
                ==> msg.content.get_rest_id() != pending_req.content.get_rest_id()
        }

    }
}

pub proof fn lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec: TempPred<Self>, key: ObjectRef)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(key)))),
{
    let invariant = Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(key);
    let stronger_next = |s, s_prime: Self| {
        Self::next()(s, s_prime)
        && Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        && Self::every_pending_req_msg_has_lower_id_than_allocator()(s)
    };
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    Self::lemma_always_every_pending_req_msg_has_lower_id_than_allocator(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_pending_req_msg_has_lower_id_than_allocator())
    );
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime) implies
    invariant(s_prime) by {
        if s_prime.ongoing_reconciles().contains_key(key) && s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some() {
            let pending_req = s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0();
            assert forall |msg: MsgType<E>| #[trigger] s_prime.in_flight().contains(msg) && msg.content.is_APIRequest() && msg != pending_req implies
            msg.content.get_rest_id() != pending_req.content.get_rest_id() by {
                let step = choose |step| Self::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        let cr_key = input.1.get_Some_0();
                        if cr_key == key {
//                            assert(pending_req.content.get_rest_id() == s.rest_id_allocator.rest_id_counter);
                            if s.in_flight().contains(msg) {} else {}
//                            assert(msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter);
                        } else {
//                            assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
//                            assert(pending_req.content.get_rest_id() < s.rest_id_allocator.rest_id_counter);
                            if s.in_flight().contains(msg) {} else {}
                        }
                    },
                    _ => {
//                        assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                        if !s.in_flight().contains(msg) {
//                            assert(pending_req.content.get_rest_id() < s.rest_id_allocator.rest_id_counter);
//                            assert(msg.content.get_rest_id() == s.rest_id_allocator.rest_id_counter)
                        }
                    }
                }
            }
        }
    };
    init_invariant::<Self>(spec, Self::init(), stronger_next, invariant);
}

pub open spec fn in_flight_msg_has_unique_id(msg: MsgType<E>) -> StatePred<Self> {
    |s: Self| {
        s.in_flight().contains(msg)
        ==> (
            forall |other_msg: MsgType<E>|
                #[trigger] s.in_flight().contains(other_msg)
                && msg != other_msg
                ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()
        )
    }
}

pub open spec fn every_in_flight_msg_has_unique_id() -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            #[trigger] s.in_flight().contains(msg)
            ==> s.in_flight().count(msg) == 1
                && (
                    forall |other_msg: MsgType<E>|
                        #[trigger] s.in_flight().contains(other_msg)
                        && msg != other_msg
                        ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()
                )
    }
}

pub proof fn lemma_always_every_in_flight_msg_has_unique_id(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
{
    let invariant = Self::every_in_flight_msg_has_unique_id();
    let stronger_next = |s, s_prime: Self| {
        Self::next()(s, s_prime)
        && Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator())
    );
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |msg: MsgType<E>| #[trigger] s_prime.in_flight().contains(msg) implies s_prime.in_flight().count(msg) == 1 &&
        (forall |other_msg: MsgType<E>| #[trigger] s_prime.in_flight().contains(other_msg) && msg != other_msg
        ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()) by {
            let step = choose |step| Self::next_step(s, s_prime, step);
            assert_by(
                s_prime.in_flight().count(msg) == 1, {
                    match step {
                        Step::ApiServerStep(input) => {
                            let req = input.get_Some_0();
                            let (_, resp) = Self::transition_by_etcd(req, s.kubernetes_api_state);
//                            assert(resp.content.get_rest_id() == req.content.get_rest_id());
//                            assert(s.in_flight().contains(req));
                            if s.in_flight().contains(msg) {
//                                assert(s.in_flight().count(msg) == 1);
//                                assert(msg.content.get_rest_id() != resp.content.get_rest_id());
//                                assert(s_prime.in_flight().count(msg) == 1);
                            } else {
//                                assert(msg == resp);
//                                assert(s_prime.in_flight().count(resp) == 1);
                            }
                        },
                        Step::FailTransientlyStep(input) => {
                            let req = input.0;
//                            assert(s.in_flight().contains(req));
                            if s.in_flight().contains(msg) {
//                                assert(s.in_flight().count(msg) == 1);
//                                assert(s_prime.in_flight().count(msg) == 1);
                            } else {
//                                assert(s_prime.in_flight().count(msg) == 1);
                            }
                        },
                        _ => {
                            if (s.in_flight().contains(msg)) {
//                                assert(s.in_flight().count(msg) == 1);
                            }
                        },
                    }
                }
            );
            assert forall |other_msg: MsgType<E>| #[trigger] s_prime.in_flight().contains(other_msg) && msg != other_msg implies
            msg.content.get_rest_id() != other_msg.content.get_rest_id() by {
                // At most one message will be added to the network_state.in_flight for each action.
//                assert(s.in_flight().contains(msg) || s.in_flight().contains(other_msg));
                if (s.in_flight().contains(msg) && s.in_flight().contains(other_msg)) {
//                    assert(msg.content.get_rest_id() != other_msg.content.get_rest_id());
                } else {
                    if (s.in_flight().contains(msg)) {
                        Self::newly_added_msg_have_different_id_from_existing_ones(s, s_prime, msg, other_msg);
                    } else {
                        Self::newly_added_msg_have_different_id_from_existing_ones(s, s_prime, other_msg, msg);
                    }
                }
            }
        }
    };
    init_invariant::<Self>(spec, Self::init(), stronger_next, invariant);
}

proof fn newly_added_msg_have_different_id_from_existing_ones(
    s: Self, s_prime: Self, msg_1: MsgType<E>, msg_2: MsgType<E>
)
    requires
        Self::next()(s, s_prime),
        Self::every_in_flight_msg_has_lower_id_than_allocator()(s),
        s.in_flight().contains(msg_1),
        !s.in_flight().contains(msg_2),
        s_prime.in_flight().contains(msg_1),
        s_prime.in_flight().contains(msg_2),
        Self::every_in_flight_msg_has_unique_id()(s), // the invariant
    ensures msg_1.content.get_rest_id() != msg_2.content.get_rest_id(),
{
    if (msg_2.content.is_APIResponse()) {
        let next_step = choose |step: Step<MsgType<E>>| Self::next_step(s, s_prime, step);
        match next_step {
            Step::ApiServerStep(input) => {
                let req_msg = input.get_Some_0();
//                assert(s.network_state.in_flight.count(req_msg) <= 1);
//                assert(msg_1.content.get_rest_id() != msg_2.content.get_rest_id());
            }
            Step::FailTransientlyStep(input) => {
                let req_msg = input.0;
//                assert(s.network_state.in_flight.count(req_msg) <= 1);
//                assert(msg_1.content.get_rest_id() != msg_2.content.get_rest_id());
            }
            _ => assert(false),
        }
    } else if msg_2.content.is_ExternalAPIResponse() {
        let next_step = choose |step: Step<MsgType<E>>| Self::next_step(s, s_prime, step);
        match next_step {
            Step::ExternalAPIStep(input) => {
                let req_msg = input.get_Some_0();
//                assert(s.network_state.in_flight.count(req_msg) <= 1);
//                assert(msg_1.content.get_rest_id() != msg_2.content.get_rest_id());
            }
            _ => assert(false),
        }
    }
}

pub open spec fn is_ok_get_response_msg() -> spec_fn(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_ApiServer()
        && msg.content.is_get_response()
        && msg.content.get_get_response().res.is_Ok()
}

pub open spec fn is_ok_get_response_msg_and_matches_key(key: ObjectRef) -> spec_fn(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_ApiServer()
        && msg.content.is_get_response()
        && msg.content.get_get_response().res.is_Ok()
        && msg.content.get_get_response().res.get_Ok_0().object_ref() == key
}

pub open spec fn is_ok_update_response_msg() -> spec_fn(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_ApiServer()
        && msg.content.is_update_response()
        && msg.content.get_update_response().res.is_Ok()
}

pub open spec fn is_ok_update_response_msg_and_matches_key(key: ObjectRef) -> spec_fn(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_ApiServer()
        && msg.content.is_update_response()
        && msg.content.get_update_response().res.is_Ok()
        && msg.content.get_update_response().res.get_Ok_0().object_ref() == key
}

pub open spec fn is_ok_create_response_msg() -> spec_fn(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_ApiServer()
        && msg.content.is_create_response()
        && msg.content.get_create_response().res.is_Ok()
}

pub open spec fn is_ok_create_response_msg_and_matches_key(key: ObjectRef) -> spec_fn(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_ApiServer()
        && msg.content.is_create_response()
        && msg.content.get_create_response().res.is_Ok()
        && msg.content.get_create_response().res.get_Ok_0().object_ref() == key
}

pub open spec fn object_in_ok_get_response_has_smaller_rv_than_etcd() -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            s.in_flight().contains(msg)
            && #[trigger] Self::is_ok_get_response_msg()(msg)
            ==> msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
                && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
{
    let inv = Self::object_in_ok_get_response_has_smaller_rv_than_etcd();
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()),
        lift_state(Self::each_object_in_etcd_is_well_formed())
    );
//    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
////        assert forall |msg| s_prime.in_flight().contains(msg) && #[trigger] Self::is_ok_get_response_msg()(msg) implies
////        msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
////        && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() < s_prime.kubernetes_api_state.resource_version_counter by {
////            let step = choose |step| Self::next_step(s, s_prime, step);
////            if s.in_flight().contains(msg) {
//////                assert(s.kubernetes_api_state.resource_version_counter <= s_prime.kubernetes_api_state.resource_version_counter);
////            } else {
////                let input = step.get_ApiServerStep_0().get_Some_0();
////                match input.content.get_APIRequest_0() {
////                    APIRequest::GetRequest(req) => {
////                        if Self::is_ok_get_response_msg()(msg) {
////                            let req_key = req.key;
//////                            assert(s.resources().contains_key(req_key));
//////                            assert(msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() == s.resources()[req_key].metadata.resource_version.get_Some_0());
//////                            assert(s.resources()[req_key].metadata.resource_version.get_Some_0() < s_prime.kubernetes_api_state.resource_version_counter);
////                        } else {}
////                    }
////                    _ => {}
////                }
////            }
////        }
//    }
    init_invariant(spec, Self::init(), next, inv);
}

pub open spec fn object_in_ok_get_resp_is_same_as_etcd_with_same_rv(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        forall |msg|
            #[trigger] s.in_flight().contains(msg)
            && Self::is_ok_get_response_msg_and_matches_key(key)(msg)
            && s.resources().contains_key(key)
            && s.resources()[key].metadata.resource_version.get_Some_0() == msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0()
            ==> s.resources()[key] == msg.content.get_get_response().res.get_Ok_0()
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec: TempPred<Self>, key: ObjectRef)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(key)))),
{
    let inv = Self::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(key);
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
        &&& Self::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    Self::lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()), lift_state(Self::each_object_in_etcd_is_well_formed()),
        lift_state(Self::object_in_ok_get_response_has_smaller_rv_than_etcd())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && Self::is_ok_get_response_msg_and_matches_key(key)(msg) && s_prime.resources().contains_key(key)
        && s_prime.resources()[key].metadata.resource_version.get_Some_0() == msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() implies s_prime.resources()[key] == msg.content.get_get_response().res.get_Ok_0() by {
            assert(Self::is_ok_get_response_msg()(msg));
            if s.in_flight().contains(msg) {
                if !s.resources().contains_key(key) || s.resources()[key] != s_prime.resources()[key] {
//                    assert(s_prime.resources()[key].metadata.resource_version.get_Some_0() != msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0())
                }
            } else {
                let step = choose |step| Self::next_step(s, s_prime, step);
//                assert(step.is_ApiServerStep());
                let req = step.get_ApiServerStep_0().get_Some_0();
                match req.content.get_APIRequest_0() {
                    APIRequest::GetRequest(_) => {}
                    APIRequest::ListRequest(_) => {}
                    APIRequest::CreateRequest(_) => {}
                    APIRequest::DeleteRequest(_) => {}
                    APIRequest::UpdateRequest(_) => {}
                    APIRequest::UpdateStatusRequest(_) => {}
                }
//                assert(msg == Self::handle_get_request_msg(req, s.kubernetes_api_state).1);
//                assert(s.resources().contains_key(req.content.get_get_request().key));
//                assert(msg.content.get_get_response().res.get_Ok_0() == s.resources()[req.content.get_get_request().key]);
//                assert(req.content.get_get_request().key == msg.content.get_get_response().res.get_Ok_0().object_ref());
//                assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
//                assert(s_prime.resources()[key] == msg.content.get_get_response().res.get_Ok_0());
            }
        }
    }
    init_invariant(spec, Self::init(), next, inv);
}

pub open spec fn key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key: ObjectRef) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        forall |msg: MsgType<E>|
            #[trigger] s.in_flight().contains(msg)
            && Self::is_ok_get_response_msg()(msg)
            && s.ongoing_reconciles().contains_key(key)
            && s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            ==> Self::is_ok_get_response_msg_and_matches_key(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_get_request().key)(msg)
    }
}

pub proof fn lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec: TempPred<Self>, key: ObjectRef)
    requires
        key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)))),
{
    let inv = Self::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key);
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(key)(s)
        &&& Self::every_in_flight_msg_has_unique_id()(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    Self::lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, key);
    Self::lemma_always_every_in_flight_msg_has_unique_id(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()), lift_state(Self::each_object_in_etcd_is_well_formed()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(key)),
        lift_state(Self::every_in_flight_msg_has_unique_id())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && Self::is_ok_get_response_msg()(msg) && s_prime.ongoing_reconciles().contains_key(key)
        && s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some() && Message::resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) implies
        Self::is_ok_get_response_msg_and_matches_key(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_get_request().key)(msg) by {
//            assert(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.is_get_request());
            let req_key = s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_get_request().key;
            let step = choose |step| Self::next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    let cr_key = input.1.get_Some_0();
                    if cr_key == key {
//                        assert(false);
                    } else {
//                        assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
//                        assert(Self::is_ok_get_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::ApiServerStep(input) => {
//                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
//                        assert(msg.content.is_get_response());
//                        assert(msg == Self::handle_get_request_msg(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), s.kubernetes_api_state).1);
//                        assert(msg.src.is_ApiServer()
//                        && msg.content.is_get_response());
                        if msg.content.get_get_response().res.is_Ok() {
//                            assert(s.resources().contains_key(req_key));
//                            assert(s.resources()[req_key].object_ref() == req_key);
                        }
//                        assert(Self::is_ok_get_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::FailTransientlyStep(input) => {
//                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
//                        assert(msg.src.is_ApiServer());
//                        assert(msg.content.is_get_response());
//                        assert(msg.content.get_get_response().res.is_Err());
                    }
//                    assert(Self::is_ok_get_response_msg_and_matches_key(req_key)(msg));
                },
                Step::ExternalAPIStep(input) => {
//                    assert(input.get_Some_0() != msg);
                    assert(s.in_flight().contains(msg));
                },
                _ => {
                    assert(s.in_flight().contains(msg));
//                    assert(Self::is_ok_get_response_msg_and_matches_key(req_key)(msg));
                }
            }
        }
    }
    init_invariant(spec, Self::init(), next, inv);
}

pub open spec fn key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(key: ObjectRef) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        forall |msg: MsgType<E>|
            #[trigger] s.in_flight().contains(msg)
            && Self::is_ok_update_response_msg()(msg)
            && s.ongoing_reconciles().contains_key(key)
            && s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            ==> Self::is_ok_update_response_msg_and_matches_key(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_update_request().key())(msg)
    }
}

pub proof fn lemma_always_key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(spec: TempPred<Self>, key: ObjectRef)
    requires
        key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(key)))),
{
    let inv = Self::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(key);
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(key)(s)
        &&& Self::every_in_flight_msg_has_unique_id()(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    Self::lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, key);
    Self::lemma_always_every_in_flight_msg_has_unique_id(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()), lift_state(Self::each_object_in_etcd_is_well_formed()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(key)),
        lift_state(Self::every_in_flight_msg_has_unique_id())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && Self::is_ok_update_response_msg()(msg) && s_prime.ongoing_reconciles().contains_key(key)
        && s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some() && Message::resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) implies
        Self::is_ok_update_response_msg_and_matches_key(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_update_request().key())(msg) by {
//            assert(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.is_update_request());
            let req_key = s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_update_request().key();
            let step = choose |step| Self::next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    let cr_key = input.1.get_Some_0();
                    if cr_key == key {
//                        assert(false);
                    } else {
//                        assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
//                        assert(Self::is_ok_update_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::ApiServerStep(input) => {
//                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
//                        assert(msg.content.is_update_response());
//                        assert(msg == Self::handle_update_request_msg(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), s.kubernetes_api_state).1);
//                        assert(msg.src.is_ApiServer()
//                        && msg.content.is_update_response());
                        if msg.content.get_update_response().res.is_Ok() {
//                            assert(s.resources().contains_key(req_key));
//                            assert(s.resources()[req_key].object_ref() == req_key);
                        }
//                        assert(Self::is_ok_update_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::FailTransientlyStep(input) => {
//                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
//                        assert(msg.src.is_ApiServer());
//                        assert(msg.content.is_update_response());
//                        assert(msg.content.get_update_response().res.is_Err());
                    }
//                    assert(Self::is_ok_update_response_msg_and_matches_key(req_key)(msg));
                },
                Step::ExternalAPIStep(input) => {
//                    assert(input.get_Some_0() != msg);
                    assert(s.in_flight().contains(msg));
                },
                _ => {
                    assert(s.in_flight().contains(msg));
//                    assert(Self::is_ok_update_response_msg_and_matches_key(req_key)(msg));
                }
            }
        }
    }
    init_invariant(spec, Self::init(), next, inv);
}

pub open spec fn key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(key: ObjectRef) -> StatePred<Self>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        let pending_req = s.ongoing_reconciles()[key].pending_req_msg.get_Some_0();
        let create_req = pending_req.content.get_create_request();
        forall |msg: MsgType<E>|
            s.in_flight().contains(msg)
            && Self::is_ok_create_response_msg()(msg)
            && s.ongoing_reconciles().contains_key(key)
            && s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && #[trigger] Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            && create_req.obj.metadata.name.is_Some()
            ==> Self::is_ok_create_response_msg_and_matches_key(create_req.key())(msg)
    }
}

pub proof fn lemma_always_key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(spec: TempPred<Self>, key: ObjectRef)
    requires
        key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(key)))),
{
    let inv = Self::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(key);
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(key)(s)
        &&& Self::every_in_flight_msg_has_unique_id()(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    Self::lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, key);
    Self::lemma_always_every_in_flight_msg_has_unique_id(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()), lift_state(Self::each_object_in_etcd_is_well_formed()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(key)),
        lift_state(Self::every_in_flight_msg_has_unique_id())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let create_req = s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_create_request();
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && Self::is_ok_create_response_msg()(msg) && s_prime.ongoing_reconciles().contains_key(key)
        && s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some() && Message::resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
        && create_req.obj.metadata.name.is_Some()
        implies s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_create_request().obj.metadata.name.is_Some() &&
        Self::is_ok_create_response_msg_and_matches_key(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_create_request().key())(msg) by {
//            assert(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.is_create_request());
            let req_key = create_req.key();
            let step = choose |step| Self::next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    let cr_key = input.1.get_Some_0();
                    if cr_key == key {
//                        assert(false);
                    } else {
//                        assert(s.ongoing_reconciles()[key].pending_req_msg == s_prime.ongoing_reconciles()[key].pending_req_msg);
                        // assert(create_req.obj.metadata.name.is_Some());

//                        assert(Self::is_ok_create_response_msg_and_matches_key(create_req.key())(msg));
                    }
                },
                Step::ApiServerStep(input) => {
//                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
//                        assert(msg.content.is_create_response());
//                        assert(msg == Self::handle_create_request_msg(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), s.kubernetes_api_state).1);
//                        assert(msg.src.is_ApiServer()
//                        && msg.content.is_create_response());
                        if msg.content.get_create_response().res.is_Ok() {
//                            assert(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_create_request().obj.metadata.name.is_Some());
//                            assert(s_prime.resources()[req_key].object_ref() == req_key);
                        }
//                        assert(Self::is_ok_create_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::FailTransientlyStep(input) => {
//                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
//                        assert(msg.src.is_ApiServer());
//                        assert(msg.content.is_create_response());
//                        assert(msg.content.get_create_response().res.is_Err());
                    }
//                    assert(Self::is_ok_create_response_msg_and_matches_key(req_key)(msg));
                },
                Step::ExternalAPIStep(input) => {
//                    assert(input.get_Some_0() != msg);
//                    assert(s.in_flight().contains(msg));
//                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                },
                _ => {
//                    assert(s.in_flight().contains(msg));
//                    assert(Self::is_ok_create_response_msg_and_matches_key(req_key)(msg));
                }
            }
        }
    }
    init_invariant(spec, Self::init(), next, inv);
}

}

}
