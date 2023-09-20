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
    ensures
        spec.entails(always(lift_state(Self::scheduled_cr_has_lower_uid_than_uid_counter()))),
{
    let invariant = Self::scheduled_cr_has_lower_uid_than_uid_counter();
    let stronger_next = |s, s_prime| {
        Self::next()(s, s_prime)
        && Self::every_object_in_etcd_has_lower_uid_than_uid_counter()(s)
    };
    Self::lemma_always_every_object_in_etcd_has_lower_uid_than_uid_counter(spec);
    combine_spec_entails_always_n!(spec, lift_action(stronger_next), lift_action(Self::next()), lift_state(Self::every_object_in_etcd_has_lower_uid_than_uid_counter()));
    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        // if s_prime.controller_state.scheduled_reconciles.contains_key(key) {
            assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
            K::marshal_preserves_metadata();
        // }
    }
    init_invariant(spec, Self::init(), stronger_next, invariant);
}

pub open spec fn triggering_cr_has_lower_uid_than_uid_counter() -> StatePred<Self>
{
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
    ensures
        spec.entails(always(lift_state(Self::triggering_cr_has_lower_uid_than_uid_counter()))),
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

pub open spec fn resp_matches_at_most_one_pending_req(
    resp_msg: MsgType<E>, cr_key: ObjectRef
) -> StatePred<Self> {
    |s: Self| {
        s.ongoing_reconciles().contains_key(cr_key)
        && Self::pending_k8s_api_req_msg(s, cr_key)
        && Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0())
        ==> (
            forall |other_key: ObjectRef|
                #[trigger] s.ongoing_reconciles().contains_key(other_key)
                && Self::pending_k8s_api_req_msg(s, other_key)
                && other_key != cr_key
                ==> !Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[other_key].pending_req_msg.get_Some_0())
            )
    }
}

pub open spec fn resp_if_matches_pending_req_then_no_other_resp_matches(
    resp_msg: MsgType<E>, cr_key: ObjectRef
) -> StatePred<Self> {
    |s: Self| {
        s.ongoing_reconciles().contains_key(cr_key)
        && s.in_flight().contains(resp_msg)
        && Self::pending_k8s_api_req_msg(s, cr_key)
        && Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0())
        ==> (
            forall |other_resp: MsgType<E>| other_resp != resp_msg && #[trigger] s.in_flight().contains(other_resp)
            ==> !Message::resp_msg_matches_req_msg(other_resp, s.ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0())
        )
    }
}

pub proof fn lemma_always_resp_if_matches_pending_req_then_no_other_resp_matches(
    spec: TempPred<Self>, resp_msg: MsgType<E>, cr_key: ObjectRef
)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(
            always(lift_state(Self::resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key)))
        ),
{
    implies_preserved_by_always::<Self>(
        Self::every_in_flight_msg_has_unique_id(), Self::resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key)
    );
    Self::lemma_always_every_in_flight_msg_has_unique_id(spec);
    entails_trans::<Self>(
        spec,
        always(lift_state(Self::every_in_flight_msg_has_unique_id())),
        always(lift_state(Self::resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key)))
    );
}

pub proof fn lemma_forall_always_resp_if_matches_pending_req_then_no_other_resp_matches(
    spec: TempPred<Self>, cr_key: ObjectRef
)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(
            tla_forall(|resp_msg: MsgType<E>| always(lift_state(Self::resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key))))
        ),
{
    let m_to_p = |msg| always(lift_state(Self::resp_if_matches_pending_req_then_no_other_resp_matches(msg, cr_key)));
    assert forall |msg| #[trigger] spec.entails(m_to_p(msg)) by {
        Self::lemma_always_resp_if_matches_pending_req_then_no_other_resp_matches(spec, msg, cr_key);
    }
    spec_entails_tla_forall(spec, m_to_p);
}

pub open spec fn each_resp_if_matches_pending_req_then_no_other_resp_matches(
    cr_key: ObjectRef
) -> StatePred<Self>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        forall |resp_msg: MsgType<E>|
            s.ongoing_reconciles().contains_key(cr_key)
            && #[trigger] s.in_flight().contains(resp_msg)
            && Self::pending_k8s_api_req_msg(s, cr_key)
            && Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0())
            ==> (
                forall |other_resp: MsgType<E>| other_resp != resp_msg && #[trigger] s.in_flight().contains(other_resp)
                ==> !Message::resp_msg_matches_req_msg(other_resp, s.ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0())
            )
    }
}

pub proof fn lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches(
    spec: TempPred<Self>, cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(
            always(lift_state(Self::each_resp_if_matches_pending_req_then_no_other_resp_matches(cr_key)))
        ),
{
    let forall_a_to_p = lift_state(Self::each_resp_if_matches_pending_req_then_no_other_resp_matches(cr_key));
    let a_to_p = |resp_msg: MsgType<E>| lift_state(Self::resp_if_matches_pending_req_then_no_other_resp_matches(resp_msg, cr_key));
    let a_to_always_p = |resp_msg: MsgType<E>| always(a_to_p(resp_msg));
    assert forall |resp_msg: MsgType<E>| spec.entails(#[trigger] a_to_always_p(resp_msg))
    by {
        Self::lemma_always_resp_if_matches_pending_req_then_no_other_resp_matches(spec, resp_msg, cr_key);
    }
    spec_entails_tla_forall(spec, a_to_always_p);
    tla_forall_always_equality(a_to_p);

    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies forall_a_to_p.satisfied_by(ex) by {
        assert forall |resp_msg: MsgType<E>|
            ex.head().ongoing_reconciles().contains_key(cr_key)
            && #[trigger] ex.head().in_flight().contains(resp_msg)
            && Self::pending_k8s_api_req_msg(ex.head(), cr_key)
            && Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0())
            ==> (
                forall |other_resp: MsgType<E>| other_resp != resp_msg && #[trigger] ex.head().in_flight().contains(other_resp)
                ==> !Message::resp_msg_matches_req_msg(other_resp, ex.head().ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0())
            )
        by {
            assert(a_to_p(resp_msg).satisfied_by(ex));
        }
    }

    temp_pred_equality(forall_a_to_p, tla_forall(a_to_p));

}

pub proof fn lemma_always_resp_matches_at_most_one_pending_req(
    spec: TempPred<Self>, resp_msg: MsgType<E>, cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::resp_matches_at_most_one_pending_req(resp_msg, cr_key)))),
{
    let invariant = Self::resp_matches_at_most_one_pending_req(resp_msg, cr_key);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::pending_req_has_lower_req_id_than_allocator()(s)
    };

    Self::lemma_always_pending_req_has_lower_req_id_than_allocator(spec);

    strengthen_next::<Self>(
        spec, Self::next(), Self::pending_req_has_lower_req_id_than_allocator(), stronger_next
    );
    init_invariant::<Self>(spec, Self::init(), stronger_next, invariant);
}

pub proof fn lemma_forall_resp_always_matches_at_most_one_pending_req(
    spec: TempPred<Self>, cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(
            tla_forall(|msg| always(lift_state(Self::resp_matches_at_most_one_pending_req(msg, cr_key))))
        ),
{
    let m_to_p = |msg| always(lift_state(Self::resp_matches_at_most_one_pending_req(msg, cr_key)));
    assert forall |msg| #[trigger] spec.entails(m_to_p(msg)) by {
        Self::lemma_always_resp_matches_at_most_one_pending_req(spec, msg, cr_key);
    };
    spec_entails_tla_forall(spec, m_to_p);
}

pub open spec fn each_resp_matches_at_most_one_pending_req(
    cr_key: ObjectRef
) -> StatePred<Self>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: Self| {
        forall |resp_msg: MsgType<E>|
            s.ongoing_reconciles().contains_key(cr_key)
            && Self::pending_k8s_api_req_msg(s, cr_key)
            && #[trigger] Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0())
            ==> (
                forall |other_key: ObjectRef|
                    #[trigger] s.ongoing_reconciles().contains_key(other_key)
                    && Self::pending_k8s_api_req_msg(s, other_key)
                    && other_key != cr_key
                    ==> !Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[other_key].pending_req_msg.get_Some_0())
                )
    }
}

pub proof fn lemma_always_each_resp_matches_at_most_one_pending_req(
    spec: TempPred<Self>, cr_key: ObjectRef
)
    requires
        cr_key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::each_resp_matches_at_most_one_pending_req(cr_key)))),
{
    let invariant = Self::each_resp_matches_at_most_one_pending_req(cr_key);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::pending_req_has_lower_req_id_than_allocator()(s)
    };

    Self::lemma_always_pending_req_has_lower_req_id_than_allocator(spec);

    strengthen_next::<Self>(
        spec, Self::next(), Self::pending_req_has_lower_req_id_than_allocator(), stronger_next
    );
    init_invariant::<Self>(spec, Self::init(), stronger_next, invariant);
}

// This lemma ensures that if a controller is at some reconcile state for a cr, there must be the pending request of the
// reconcile state in flight or a corresponding response in flight.
// Obviously, this requires that when controller enters the 'state' in reconcile_core, there must be a request generated;
// otherwise, the pending request may not be there.
// The proof is very straightforward:
//   - Right after the controller enters 'state', the pending request is added to in_flight.
//   - If the pending request is processed by kubernetes api, there will be a response in flight.
//   - If the response is processed by the controller, the controller will create a new pending request in flight which
//   allows the invariant to still hold.
pub proof fn lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
    spec: TempPred<Self>, key: ObjectRef, state: FnSpec(R::T) -> bool
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
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_resp_matches_at_most_one_pending_req(key)(s)
    };
    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        if Self::at_expected_reconcile_states(key, state)(s_prime) {
            let next_step = choose |step| Self::next_step(s, s_prime, step);
            assert(!next_step.is_RestartController());
            let resp = choose |msg| {
                #[trigger] s.in_flight().contains(msg)
                && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            };
            match next_step {
                Step::KubernetesAPIStep(input) => {
                    if input == Some(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
                        let resp_msg = Self::transition_by_etcd(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), s.kubernetes_api_state).1;
                        assert(s_prime.in_flight().contains(resp_msg));
                    } else {
                        if !s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
                            assert(s_prime.in_flight().contains(resp));
                        }
                    }
                }
                Step::BuiltinControllersStep(input) => {
                    if s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                    } else {
                        assert(s_prime.in_flight().contains(resp));
                    }
                }
                Step::KubernetesBusy(input) => {
                    if input == Some(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
                        let resp_msg = Message::form_matched_err_resp_msg(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0(), APIError::ServerTimeout);
                        assert(s_prime.in_flight().contains(resp_msg));
                    } else {
                        if !s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
                            assert(s_prime.in_flight().contains(resp));
                        }
                    }
                }
                Step::ControllerStep(input) => {
                    let cr_key = input.1.get_Some_0();
                    if cr_key != key {
                        if s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
                            assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                        } else {
                            assert(s_prime.in_flight().contains(resp));
                        }
                    } else {
                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                    }
                }
                Step::ClientStep() => {
                    if s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                    } else {
                        assert(s_prime.in_flight().contains(resp));
                    }
                }
                Step::ExternalAPIStep(input) => {
                    if s.in_flight().contains(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()) {
                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                    } else {
                        assert(s_prime.in_flight().contains(resp));
                    }
                }
                _ => {
                    assert(invariant(s_prime));
                }
            }
        }
    }
    strengthen_next::<Self>(spec, Self::next(), Self::each_resp_matches_at_most_one_pending_req(key), stronger_next);
    init_invariant::<Self>(spec, Self::init(), stronger_next, invariant);
}

pub proof fn lemma_always_no_pending_req_msg_or_external_api_input_at_reconcile_state(
    spec: TempPred<Self>, key: ObjectRef, state: FnSpec(R::T) -> bool
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
    assert forall |s, s_prime: Self| invariant(s) &&
    #[trigger] Self::next()(s, s_prime) implies invariant(s_prime) by {
        if s_prime.ongoing_reconciles().contains_key(key) && state(s_prime.ongoing_reconciles()[key].local_state) {
            if s.controller_state == s_prime.controller_state {
                assert(s.ongoing_reconciles()[key].pending_req_msg.is_None());
                assert(s_prime.ongoing_reconciles()[key].pending_req_msg.is_None());
            } else {
                assert(s_prime.ongoing_reconciles()[key].pending_req_msg.is_None());
            }
        }
    }
    init_invariant(spec, Self::init(), Self::next(), invariant);
}

pub proof fn lemma_always_pending_req_msg_is_none_at_reconcile_state(
    spec: TempPred<Self>, key: ObjectRef, state: FnSpec(R::T) -> bool
)
    requires
        forall |cr, resp_o, pre_state| #[trigger] state(R::reconcile_core(cr, resp_o, pre_state).0)
            ==> {
                let req = R::reconcile_core(cr, resp_o, pre_state).1;
                req.is_None()
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
