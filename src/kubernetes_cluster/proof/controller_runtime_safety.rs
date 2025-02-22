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

pub open spec fn scheduled_cr_has_lower_uid_than_uid_counter() -> StatePred<Self> {
    |s: Self| {
        forall |key: ObjectRef|
        #[trigger] s.controller_state.scheduled_reconciles.contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> s.controller_state.scheduled_reconciles[key].metadata().uid.is_Some()
        && s.controller_state.scheduled_reconciles[key].metadata().uid.get_Some_0() < s.kubernetes_api_state.uid_counter
    }
}

pub proof fn lemma_always_scheduled_cr_has_lower_uid_than_uid_counter(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::scheduled_cr_has_lower_uid_than_uid_counter()))),
{
    let invariant = Self::scheduled_cr_has_lower_uid_than_uid_counter();
    let stronger_next = |s, s_prime| {
        Self::next()(s, s_prime)
        && Self::each_object_in_etcd_is_well_formed()(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    strengthen_next(spec, Self::next(), Self::each_object_in_etcd_is_well_formed(), stronger_next);
    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
//        assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
        K::marshal_preserves_metadata();
    }
    init_invariant(spec, Self::init(), stronger_next, invariant);
}

pub open spec fn triggering_cr_has_lower_uid_than_uid_counter() -> StatePred<Self> {
    |s: Self| {
        forall |key: ObjectRef|
        #[trigger] s.ongoing_reconciles().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> s.ongoing_reconciles()[key].triggering_cr.metadata().uid.is_Some()
        && s.ongoing_reconciles()[key].triggering_cr.metadata().uid.get_Some_0() < s.kubernetes_api_state.uid_counter
    }
}

pub proof fn lemma_always_triggering_cr_has_lower_uid_than_uid_counter(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::triggering_cr_has_lower_uid_than_uid_counter()))),
{
    let invariant = Self::triggering_cr_has_lower_uid_than_uid_counter();
    let stronger_next = |s, s_prime| {
        Self::next()(s, s_prime)
        && Self::scheduled_cr_has_lower_uid_than_uid_counter()(s)
    };
    Self::lemma_always_scheduled_cr_has_lower_uid_than_uid_counter(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(Self::next()), lift_state(Self::scheduled_cr_has_lower_uid_than_uid_counter())
    );
    init_invariant(spec, Self::init(), stronger_next, invariant);
}

// This lemma ensures that if a controller is at some reconcile state for a cr, there must be the pending request of the
// reconcile state in flight or a corresponding response in flight.
// Obviously, this requires that when controller enters the 'state' in reconcile_core, there must be a request generated;
// otherwise, the pending request may not be there.
// The proof is very straightforward:
//   - Right after the controller enters 'state', the pending request is added to in_flight.
//   - If the pending request is processed by kubernetes api, there will be a response in flight.
//   - If the pending request is processed by external api, there will be a response in flight.
//   - If the response is processed by the controller, the controller will create a new pending request in flight which
//   allows the invariant to still hold.

// TODO: broken by pod_event; Xudong will fix it later
#[verifier(external_body)]
pub proof fn lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<Self>, key: ObjectRef, state: spec_fn(R::T) -> bool)
    requires
        forall |s| (#[trigger] state(s)) ==> s != R::reconcile_init_state(),
        forall |cr, resp_o, pre_state| #[trigger] state(R::reconcile_core(cr, resp_o, pre_state).0)
            ==> R::reconcile_core(cr, resp_o, pre_state).1.is_Some(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(key)))),
    ensures spec.entails(always(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(key, state)))),
{
    let invariant = Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(key, state);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::pending_req_of_key_is_unique_with_unique_id(key)(s)
    };
//    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
//        if Self::at_expected_reconcile_states(key, state)(s_prime) {
//            let next_step = choose |step| Self::next_step(s, s_prime, step);
////            assert(!next_step.is_RestartController());
//            let resp = choose |msg| {
//                #[trigger] s.in_flight().contains(msg)
//                && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
//            };
//            match next_step {
//                Step::ApiServerStep(input) => {
//                    if input == Some(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
//                        let resp_msg = Self::transition_by_etcd(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), s.kubernetes_api_state).1;
////                        assert(s_prime.in_flight().contains(resp_msg));
//                    } else {
//                        if !s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
////                            assert(s_prime.in_flight().contains(resp));
//                        }
//                    }
//                }
//                Step::BuiltinControllersStep(input) => {
//                    if s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
////                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
//                    } else {
////                        assert(s_prime.in_flight().contains(resp));
//                    }
//                }
//                Step::FailTransientlyStep(input) => {
//                    if input.0 == s.ongoing_reconciles()[key].pending_req_msg.get_Some_0() {
//                        let resp_msg = Message::form_matched_err_resp_msg(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), input.1);
////                        assert(s_prime.in_flight().contains(resp_msg));
//                    } else {
//                        if !s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
////                            assert(s_prime.in_flight().contains(resp));
//                        }
//                    }
//                }
//                Step::ControllerStep(input) => {
//                    let cr_key = input.1.get_Some_0();
//                    if cr_key != key {
//                        if s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
////                            assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
//                        } else {
////                            assert(s_prime.in_flight().contains(resp));
//                        }
//                    } else {
////                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
//                    }
//                }
//                Step::ClientStep() => {
//                    if s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
////                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
//                    } else {
////                        assert(s_prime.in_flight().contains(resp));
//                    }
//                }
//                Step::ExternalAPIStep(input) => {
//                    if input == Some(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
//                        let resp_msg = Self::handle_external_request_helper(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), s.external_api_state, s.kubernetes_api_state.resources).1;
////                        assert(s_prime.in_flight().contains(resp_msg));
//                    } else {
//                        if !s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
////                            assert(s_prime.in_flight().contains(resp));
//                        }
//                    }
//                }
//                _ => {
////                    assert(invariant(s_prime));
//                }
//            }
//        }
//    }
    strengthen_next::<Self>(spec, Self::next(), Self::pending_req_of_key_is_unique_with_unique_id(key), stronger_next);
    init_invariant::<Self>(spec, Self::init(), stronger_next, invariant);
}

pub proof fn lemma_always_no_pending_req_msg_at_reconcile_state(spec: TempPred<Self>, key: ObjectRef, state: spec_fn(R::T) -> bool)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
        forall |cr, resp_o, pre_state|
            #[trigger] state(R::reconcile_core(cr, resp_o, pre_state).0)
            ==> R::reconcile_core(cr, resp_o, pre_state).1.is_None(),
    ensures spec.entails(always(lift_state(Self::no_pending_req_msg_at_reconcile_state(key, state)))),
{
    let invariant = Self::no_pending_req_msg_at_reconcile_state(key, state);
//    assert forall |s, s_prime: Self| invariant(s) &&
//    #[trigger] Self::next()(s, s_prime) implies invariant(s_prime) by {
//        if s_prime.ongoing_reconciles().contains_key(key) && state(s_prime.ongoing_reconciles()[key].local_state) {
//            if s.controller_state == s_prime.controller_state {
////                assert(s.ongoing_reconciles()[key].pending_req_msg.is_None());
////                assert(s_prime.ongoing_reconciles()[key].pending_req_msg.is_None());
//            } else {
////                assert(s_prime.ongoing_reconciles()[key].pending_req_msg.is_None());
//            }
//        }
//    }
    init_invariant(spec, Self::init(), Self::next(), invariant);
}

}

}