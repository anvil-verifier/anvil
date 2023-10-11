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
            #[trigger] s.in_flight().contains(msg)
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
    assert forall |msg: MsgType<E>| #[trigger] s_prime.in_flight().contains(msg) implies
    msg.content.get_rest_id() < s_prime.rest_id_allocator.rest_id_counter by {
        assert(s.rest_id_allocator.rest_id_counter <= s_prime.rest_id_allocator.rest_id_counter);
        if (s.in_flight().contains(msg)) {
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
                            match req_msg.content.get_APIRequest_0() {
                                APIRequest::GetRequest(_) => {}
                                APIRequest::ListRequest(_) => {}
                                APIRequest::CreateRequest(_) => {}
                                APIRequest::DeleteRequest(_) => {}
                                APIRequest::UpdateRequest(_) => {}
                                APIRequest::UpdateStatusRequest(_) => {}
                            }
                            assert(s.in_flight().contains(req_msg));
                            assert(id == req_msg.content.get_rest_id());
                        }
                        Step::FailTransientlyStep(input) => {
                            let req_msg = input.0;
                            assert(s.in_flight().contains(req_msg));
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
                            assert(s.in_flight().contains(req_msg));
                            assert(s.in_flight().contains(req_msg) ==> req_msg.content.get_rest_id() < s.rest_id_allocator.rest_id_counter);
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
            && #[trigger] s.in_flight().contains(msg)
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
        (msg.content.is_APIRequest() || msg.content.is_ExternalAPIRequest()) && #[trigger] s_prime.in_flight().contains(msg) implies
        s_prime.network_state.in_flight.count(msg) == 1 by {
            if (s.in_flight().contains(msg)) {
                assert(s.network_state.in_flight.count(msg) == 1);
            }
        };
    };
    init_invariant::<Self>(spec, Self::init(), stronger_next, invariant);
}

pub open spec fn in_flight_or_pending_req_message(s: Self, msg: MsgType<E>) -> bool {
    msg.content.is_APIRequest()
    && (s.in_flight().contains(msg)
    || (
        exists |key|
            #[trigger] s.ongoing_reconciles().contains_key(key)
            && s.ongoing_reconciles()[key].pending_req_msg == Some(msg)
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
            #[trigger] s.in_flight().contains(msg)
            ==> (
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
    assert forall |msg: MsgType<E>| #[trigger] s_prime.in_flight().contains(msg) implies
    (forall |other_msg: MsgType<E>| #[trigger] s_prime.in_flight().contains(other_msg) && msg != other_msg
        ==> msg.content.get_rest_id() != other_msg.content.get_rest_id()) by {
        assert forall |other_msg: MsgType<E>| #[trigger] s_prime.in_flight().contains(other_msg) && msg != other_msg implies
        msg.content.get_rest_id() != other_msg.content.get_rest_id() by {
            // At most one message will be added to the network_state.in_flight for each action.
            assert(s.in_flight().contains(msg) || s.in_flight().contains(other_msg));
            if (s.in_flight().contains(msg) && s.in_flight().contains(other_msg)) {
                assert(msg.content.get_rest_id() != other_msg.content.get_rest_id());
            } else {
                if (s.in_flight().contains(msg)) {
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
        s.in_flight().contains(msg_1),
        !s.in_flight().contains(msg_2),
        s_prime.in_flight().contains(msg_1),
        s_prime.in_flight().contains(msg_2),
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
            Step::FailTransientlyStep(input) => {
                let req_msg = input.0;
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
            #[trigger] s.ongoing_reconciles().contains_key(cr_key)
            && Self::pending_k8s_api_req_msg(s, cr_key)
            ==> s.ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0().content.get_rest_id() < s.rest_id_allocator.rest_id_counter
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

pub open spec fn is_ok_get_response_msg() -> FnSpec(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_KubernetesAPI()
        && msg.content.is_get_response()
        && msg.content.get_get_response().res.is_Ok()
}

pub open spec fn is_ok_get_response_msg_and_matches_key(key: ObjectRef) -> FnSpec(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_KubernetesAPI()
        && msg.content.is_get_response()
        && msg.content.get_get_response().res.is_Ok()
        && msg.content.get_get_response().res.get_Ok_0().object_ref() == key
}

pub open spec fn is_ok_update_response_msg() -> FnSpec(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_KubernetesAPI()
        && msg.content.is_update_response()
        && msg.content.get_update_response().res.is_Ok()
}

pub open spec fn is_ok_update_response_msg_and_matches_key(key: ObjectRef) -> FnSpec(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_KubernetesAPI()
        && msg.content.is_update_response()
        && msg.content.get_update_response().res.is_Ok()
        && msg.content.get_update_response().res.get_Ok_0().object_ref() == key
}

pub open spec fn is_ok_create_response_msg() -> FnSpec(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_KubernetesAPI()
        && msg.content.is_create_response()
        && msg.content.get_create_response().res.is_Ok()
}

pub open spec fn is_ok_create_response_msg_and_matches_key(key: ObjectRef) -> FnSpec(MsgType<E>) -> bool {
    |msg: MsgType<E>|
        msg.src.is_KubernetesAPI()
        && msg.content.is_create_response()
        && msg.content.get_create_response().res.is_Ok()
        && msg.content.get_create_response().res.get_Ok_0().object_ref() == key
}

pub open spec fn object_in_ok_get_response_has_smaller_rv_than_etcd() -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            #[trigger] s.in_flight().contains(msg)
            && Self::is_ok_get_response_msg()(msg)
            ==> msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
                && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
    }
}

pub proof fn lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
{
    let inv = Self::object_in_ok_get_response_has_smaller_rv_than_etcd();
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
        &&& Self::each_object_in_etcd_is_well_formed()(s_prime)
        &&& Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(Self::each_object_in_etcd_is_well_formed()));
    Self::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()),
        lift_state(Self::each_object_in_etcd_is_well_formed()),
        later(lift_state(Self::each_object_in_etcd_is_well_formed())),
        lift_state(Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && Self::is_ok_get_response_msg()(msg) implies
        msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
        && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() < s_prime.kubernetes_api_state.resource_version_counter by {
            let step = choose |step| Self::next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                let input = step.get_KubernetesAPIStep_0().get_Some_0();
                match input.content.get_APIRequest_0() {
                    APIRequest::GetRequest(_) => {}
                    APIRequest::ListRequest(_) => {}
                    APIRequest::CreateRequest(_) => {}
                    APIRequest::DeleteRequest(_) => {}
                    APIRequest::UpdateRequest(_) => {}
                    APIRequest::UpdateStatusRequest(_) => {}
                }
                assert(s.kubernetes_api_state.resource_version_counter <= s_prime.kubernetes_api_state.resource_version_counter);
            } else {
                let input = step.get_KubernetesAPIStep_0().get_Some_0();
                match input.content.get_APIRequest_0() {
                    APIRequest::GetRequest(_) => {}
                    APIRequest::ListRequest(_) => {}
                    APIRequest::CreateRequest(_) => {}
                    APIRequest::DeleteRequest(_) => {}
                    APIRequest::UpdateRequest(_) => {}
                    APIRequest::UpdateStatusRequest(_) => {}
                }
                let req_key = input.content.get_get_request().key;
                assert(s.resources().contains_key(req_key));
                assert(msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() == s.resources()[req_key].metadata.resource_version.get_Some_0());
                assert(s.resources()[req_key].metadata.resource_version.get_Some_0() < s_prime.kubernetes_api_state.resource_version_counter);
            }
        }
    }
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

pub proof fn lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec: TempPred<Self>, key: ObjectRef)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(key)))),
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
            if s.in_flight().contains(msg) {
                if !s.resources().contains_key(key) || s.resources()[key] != s_prime.resources()[key] {
                    assert(s_prime.resources()[key].metadata.resource_version.get_Some_0() != msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0())
                }
            } else {
                let step = choose |step| Self::next_step(s, s_prime, step);
                assert(step.is_KubernetesAPIStep());
                let req = step.get_KubernetesAPIStep_0().get_Some_0();
                match req.content.get_APIRequest_0() {
                    APIRequest::GetRequest(_) => {}
                    APIRequest::ListRequest(_) => {}
                    APIRequest::CreateRequest(_) => {}
                    APIRequest::DeleteRequest(_) => {}
                    APIRequest::UpdateRequest(_) => {}
                    APIRequest::UpdateStatusRequest(_) => {}
                }
                assert(msg == Self::handle_get_request(req, s.kubernetes_api_state).1);
                assert(s.resources().contains_key(req.content.get_get_request().key));
                assert(msg.content.get_get_response().res.get_Ok_0() == s.resources()[req.content.get_get_request().key]);
                assert(req.content.get_get_request().key == msg.content.get_get_response().res.get_Ok_0().object_ref());
                assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
                assert(s_prime.resources()[key] == msg.content.get_get_response().res.get_Ok_0());
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
    ensures
        spec.entails(always(lift_state(Self::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)))),
{
    let inv = Self::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key);
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Self::every_in_flight_or_pending_req_msg_has_unique_id()(s)
        &&& Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& Self::each_resp_if_matches_pending_req_then_no_other_resp_matches(key)(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    Self::lemma_always_every_in_flight_or_pending_req_msg_has_unique_id(spec);
    Self::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    Self::lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches(spec, key);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()), lift_state(Self::each_object_in_etcd_is_well_formed()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_or_pending_req_msg_has_unique_id()),
        lift_state(Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(Self::each_resp_if_matches_pending_req_then_no_other_resp_matches(key))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && Self::is_ok_get_response_msg()(msg) && s_prime.ongoing_reconciles().contains_key(key)
        && s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some() && Message::resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) implies
        Self::is_ok_get_response_msg_and_matches_key(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_get_request().key)(msg) by {
            assert(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.is_get_request());
            let req_key = s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_get_request().key;
            let step = choose |step| Self::next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    let cr_key = input.1.get_Some_0();
                    if cr_key == key {
                        assert(false);
                    } else {
                        assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                        assert(Self::is_ok_get_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::KubernetesAPIStep(input) => {
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
                        assert(Self::in_flight_or_pending_req_message(s, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                        assert(Self::in_flight_or_pending_req_message(s, input.get_Some_0()));
                        assert(msg.content.is_get_response());
                        assert(msg == Self::handle_get_request(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), s.kubernetes_api_state).1);
                        assert(msg.src.is_KubernetesAPI()
                        && msg.content.is_get_response());
                        if msg.content.get_get_response().res.is_Ok() {
                            assert(s.resources().contains_key(req_key));
                            assert(s.resources()[req_key].object_ref() == req_key);
                        }
                        assert(Self::is_ok_get_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::FailTransientlyStep(input) => {
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
                        assert(Self::in_flight_or_pending_req_message(s, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                        assert(Self::in_flight_or_pending_req_message(s, input.0));
                        assert(msg.src.is_KubernetesAPI());
                        assert(msg.content.is_get_response());
                        assert(msg.content.get_get_response().res.is_Err());
                    }
                    assert(Self::is_ok_get_response_msg_and_matches_key(req_key)(msg));
                },
                Step::ExternalAPIStep(input) => {
                    assert(input.get_Some_0() != msg);
                    assert(s.in_flight().contains(msg));
                },
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(Self::is_ok_get_response_msg_and_matches_key(req_key)(msg));
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
    ensures
        spec.entails(always(lift_state(Self::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(key)))),
{
    let inv = Self::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(key);
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Self::every_in_flight_or_pending_req_msg_has_unique_id()(s)
        &&& Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& Self::each_resp_if_matches_pending_req_then_no_other_resp_matches(key)(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    Self::lemma_always_every_in_flight_or_pending_req_msg_has_unique_id(spec);
    Self::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    Self::lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches(spec, key);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()), lift_state(Self::each_object_in_etcd_is_well_formed()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_or_pending_req_msg_has_unique_id()),
        lift_state(Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(Self::each_resp_if_matches_pending_req_then_no_other_resp_matches(key))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && Self::is_ok_update_response_msg()(msg) && s_prime.ongoing_reconciles().contains_key(key)
        && s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some() && Message::resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) implies
        Self::is_ok_update_response_msg_and_matches_key(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_update_request().key())(msg) by {
            assert(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.is_update_request());
            let req_key = s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_update_request().key();
            let step = choose |step| Self::next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    let cr_key = input.1.get_Some_0();
                    if cr_key == key {
                        assert(false);
                    } else {
                        assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                        assert(Self::is_ok_update_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::KubernetesAPIStep(input) => {
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
                        assert(Self::in_flight_or_pending_req_message(s, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                        assert(Self::in_flight_or_pending_req_message(s, input.get_Some_0()));
                        assert(msg.content.is_update_response());
                        assert(msg == Self::handle_update_request(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), s.kubernetes_api_state).1);
                        assert(msg.src.is_KubernetesAPI()
                        && msg.content.is_update_response());
                        if msg.content.get_update_response().res.is_Ok() {
                            assert(s.resources().contains_key(req_key));
                            assert(s.resources()[req_key].object_ref() == req_key);
                        }
                        assert(Self::is_ok_update_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::FailTransientlyStep(input) => {
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
                        assert(Self::in_flight_or_pending_req_message(s, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                        assert(Self::in_flight_or_pending_req_message(s, input.0));
                        assert(msg.src.is_KubernetesAPI());
                        assert(msg.content.is_update_response());
                        assert(msg.content.get_update_response().res.is_Err());
                    }
                    assert(Self::is_ok_update_response_msg_and_matches_key(req_key)(msg));
                },
                Step::ExternalAPIStep(input) => {
                    assert(input.get_Some_0() != msg);
                    assert(s.in_flight().contains(msg));
                },
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(Self::is_ok_update_response_msg_and_matches_key(req_key)(msg));
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
            #[trigger] s.in_flight().contains(msg)
            && Self::is_ok_create_response_msg()(msg)
            && s.ongoing_reconciles().contains_key(key)
            && s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && Message::resp_msg_matches_req_msg(msg, pending_req)
            ==> (create_req.obj.metadata.name.is_Some()
                && Self::is_ok_create_response_msg_and_matches_key(create_req.key())(msg))
    }
}

pub proof fn lemma_always_key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(spec: TempPred<Self>, key: ObjectRef)
    requires
        key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(key)))),
{
    let inv = Self::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(key);
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Self::every_in_flight_or_pending_req_msg_has_unique_id()(s)
        &&& Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& Self::each_resp_if_matches_pending_req_then_no_other_resp_matches(key)(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    Self::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    Self::lemma_always_every_in_flight_or_pending_req_msg_has_unique_id(spec);
    Self::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    Self::lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches(spec, key);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()), lift_state(Self::each_object_in_etcd_is_well_formed()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_or_pending_req_msg_has_unique_id()),
        lift_state(Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(Self::each_resp_if_matches_pending_req_then_no_other_resp_matches(key))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && Self::is_ok_create_response_msg()(msg) && s_prime.ongoing_reconciles().contains_key(key)
        && s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some() && Message::resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) implies s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_create_request().obj.metadata.name.is_Some() &&
        Self::is_ok_create_response_msg_and_matches_key(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_create_request().key())(msg) by {
            assert(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.is_create_request());
            let create_req = s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_create_request();
            let req_key = create_req.key();
            let step = choose |step| Self::next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    let cr_key = input.1.get_Some_0();
                    if cr_key == key {
                        assert(false);
                    } else {
                        assert(s.ongoing_reconciles()[key].pending_req_msg == s_prime.ongoing_reconciles()[key].pending_req_msg);
                        assert(create_req.obj.metadata.name.is_Some());
                        assert(Self::is_ok_create_response_msg_and_matches_key(create_req.key())(msg));
                    }
                },
                Step::KubernetesAPIStep(input) => {
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
                        assert(Self::in_flight_or_pending_req_message(s, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                        assert(Self::in_flight_or_pending_req_message(s, input.get_Some_0()));
                        assert(msg.content.is_create_response());
                        assert(msg == Self::handle_create_request(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), s.kubernetes_api_state).1);
                        assert(msg.src.is_KubernetesAPI()
                        && msg.content.is_create_response());
                        if msg.content.get_create_response().res.is_Ok() {
                            assert(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0().content.get_create_request().obj.metadata.name.is_Some());
                            assert(s_prime.resources()[req_key].object_ref() == req_key);
                        }
                        assert(Self::is_ok_create_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::FailTransientlyStep(input) => {
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    if !s.in_flight().contains(msg) {
                        assert(Self::in_flight_or_pending_req_message(s, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                        assert(Self::in_flight_or_pending_req_message(s, input.0));
                        assert(msg.src.is_KubernetesAPI());
                        assert(msg.content.is_create_response());
                        assert(msg.content.get_create_response().res.is_Err());
                    }
                    assert(Self::is_ok_create_response_msg_and_matches_key(req_key)(msg));
                },
                Step::ExternalAPIStep(input) => {
                    assert(input.get_Some_0() != msg);
                    assert(s.in_flight().contains(msg));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                },
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(Self::is_ok_create_response_msg_and_matches_key(req_key)(msg));
                }
            }
        }
    }
    init_invariant(spec, Self::init(), next, inv);
}

}

}
