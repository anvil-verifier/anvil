// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::{
    proof::{controller_runtime_safety, kubernetes_api_safety},
    spec::{
        common::*,
        controller::common::{controller_req_msg, ControllerAction, ControllerActionInput},
        distributed_system::*,
        kubernetes_api::state_machine::handle_get_request,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::simple_controller::proof::shared::*;
use crate::simple_controller::spec::{
    simple_reconciler,
    simple_reconciler::{simple_reconciler, SimpleReconcileState},
};
use crate::temporal_logic::{defs::*, rules::*};
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_always_reconcile_init_implies_no_pending_req(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(reconciler_at_init_pc(cr_key)).implies(lift_state(|s: State<SimpleReconcileState>| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
                &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
            }))
        )),
{
    let invariant = |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
        ==> s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
            && s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    // We intentionally write the safety property in a form that is friendly to liveness reasoning
    // There is no need to do this if we only want to prove safety
    let invariant_temp_pred = lift_state(reconciler_at_init_pc(cr_key)).implies(lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    }));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(invariant), invariant_temp_pred);
}

pub open spec fn reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr_key: ResourceKey) -> StatePred<State<SimpleReconcileState>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        ==> exists |req_msg| {
                #[trigger] is_controller_get_cr_request_msg(req_msg, cr_key)
                && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(req_msg)
                && (s.message_in_flight(req_msg)
                    || exists |resp_msg: Message| {
                        #[trigger] s.message_in_flight(resp_msg)
                        && resp_msg_matches_req_msg(resp_msg, req_msg)
                    })
            }
    }
}

/// If the reconcile is at get_cr_done_pc, then (1) a get cr request message is sent or (2) the corresponding response is sent.
pub proof fn lemma_always_reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(always(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr_key)))),
{
    let invariant = reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr_key);

    let stronger_next = |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(cr_key)(s)
    };

    assert forall |s, s_prime: State<SimpleReconcileState>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        next_preserves_reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr_key, s, s_prime);
    };

    controller_runtime_safety::lemma_always_each_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(simple_reconciler(), cr_key);

    entails_and_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), always(lift_action(next(simple_reconciler()))), always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(cr_key))));
    always_and_equality::<State<SimpleReconcileState>>(lift_action(next(simple_reconciler())), lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(cr_key)));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_action(next(simple_reconciler())).and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(cr_key))), lift_action(stronger_next));

    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), stronger_next, invariant);
}

proof fn next_preserves_reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr_key: ResourceKey, s: State<SimpleReconcileState>, s_prime: State<SimpleReconcileState>)
    requires
        cr_key.kind.is_CustomResourceKind(),
        reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr_key)(s),
        controller_runtime_safety::each_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(cr_key)(s),
        next(simple_reconciler())(s, s_prime),
    ensures
        reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr_key)(s_prime),
{
    if s_prime.reconcile_state_contains(cr_key) && s_prime.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc() {
        if s.reconcile_state_contains(cr_key) && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc() {
            let req_msg = choose |req_msg| #[trigger] is_controller_get_cr_request_msg(req_msg, cr_key) && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(req_msg);
            assert(is_controller_get_cr_request_msg(req_msg, cr_key) && s_prime.reconcile_state_of(cr_key).pending_req_msg === Option::Some(req_msg));
            if s.message_in_flight(req_msg) {
                if s_prime.message_in_flight(req_msg) {
                    assert(s_prime.message_in_flight(req_msg)); // providing witness for exists |req_msg| ...
                } else {
                    let (_, resp_msg, _) = handle_get_request(req_msg, s.kubernetes_api_state);
                    assert(s_prime.message_in_flight(resp_msg) && resp_msg_matches_req_msg(resp_msg, req_msg)); // providing witness for exists |resp_msg| ...
                }
            } else {
                let resp_msg = choose |resp_msg| #[trigger] s.message_in_flight(resp_msg) && resp_msg_matches_req_msg(resp_msg, req_msg);
                assert(controller_runtime_safety::resp_matches_at_most_one_pending_req::<SimpleReconcileState>(resp_msg, cr_key)(s));
                assert(s_prime.message_in_flight(resp_msg) && resp_msg_matches_req_msg(resp_msg, req_msg)); // providing witness for exists |resp_msg| ...
            }
        } else {
            let req_msg = controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key}), s.controller_state.req_id);
            assert(is_controller_get_cr_request_msg(req_msg, cr_key)
                && s_prime.reconcile_state_of(cr_key).pending_req_msg === Option::Some(req_msg)
                && s_prime.message_in_flight(req_msg)
            ); // providing witness for exists |req_msg| ...
        }
    }
}

pub open spec fn reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr_key: ResourceKey) -> StatePred<State<SimpleReconcileState>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
        ==> exists |req_msg| {
                #[trigger] is_controller_create_cm_request_msg(req_msg, cr_key)
                && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(req_msg)
                && (s.message_in_flight(req_msg) || s.resource_key_exists(simple_reconciler::subresource_configmap(cr_key).key))
            }
    }
}

/// If the reconcile is at create_cm_done_pc, then (1) a create cm request message is sent or (2) the corresponding response is sent.
pub proof fn lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr_key)))),
{
    let invariant = reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr_key);

    let stronger_next = |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& delete_cm_req_msg_not_in_flight(cr_key)(s)
    };

    assert forall |s, s_prime: State<SimpleReconcileState>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        next_preserves_reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr_key, s, s_prime);
    };

    lemma_delete_cm_req_msg_never_in_flight(cr_key);

    entails_and_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), always(lift_action(next(simple_reconciler()))), always(lift_state(delete_cm_req_msg_not_in_flight(cr_key))));
    always_and_equality::<State<SimpleReconcileState>>(lift_action(next(simple_reconciler())), lift_state(delete_cm_req_msg_not_in_flight(cr_key)));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_action(next(simple_reconciler())).and(lift_state(delete_cm_req_msg_not_in_flight(cr_key))), lift_action(stronger_next));

    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), stronger_next, invariant);
}

proof fn next_preserves_reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr_key: ResourceKey, s: State<SimpleReconcileState>, s_prime: State<SimpleReconcileState>)
    requires
        cr_key.kind.is_CustomResourceKind(),
        reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr_key)(s),
        delete_cm_req_msg_not_in_flight(cr_key)(s),
        next(simple_reconciler())(s, s_prime),
    ensures
        reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr_key)(s_prime),
{
    if s_prime.reconcile_state_contains(cr_key) && s_prime.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc() {
        if s.reconcile_state_contains(cr_key) && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc() {
            let req_msg = choose |req_msg| #[trigger] is_controller_create_cm_request_msg(req_msg, cr_key) && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(req_msg);
            assert(is_controller_create_cm_request_msg(req_msg, cr_key) && s_prime.reconcile_state_of(cr_key).pending_req_msg === Option::Some(req_msg));
            if s.message_in_flight(req_msg) {
                if s.resource_key_exists(simple_reconciler::subresource_configmap(cr_key).key) {
                    assert(s_prime.resource_key_exists(simple_reconciler::subresource_configmap(cr_key).key));
                } else {
                    if s_prime.message_in_flight(req_msg) {
                        assert(s_prime.message_in_flight(req_msg));
                    } else {
                        assert(s_prime.resource_key_exists(simple_reconciler::subresource_configmap(cr_key).key));
                    }
                }
            } else {
                assert(s_prime.resource_key_exists(simple_reconciler::subresource_configmap(cr_key).key));
            }
        } else {
            let req_msg = controller_req_msg(simple_reconciler::create_cm_req(cr_key), s.controller_state.req_id);
            assert(is_controller_create_cm_request_msg(req_msg, cr_key)
                && s_prime.reconcile_state_of(cr_key).pending_req_msg === Option::Some(req_msg)
                && s_prime.message_in_flight(req_msg)
            );
        }
    }
}

pub open spec fn delete_cm_req_msg_not_in_flight(cr_key: ResourceKey) -> StatePred<State<SimpleReconcileState>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<SimpleReconcileState>| {
        !exists |m: Message| {
            &&& #[trigger] s.message_in_flight(m)
            &&& m.dst === HostId::KubernetesAPI
            &&& m.is_delete_request()
            &&& m.get_delete_request().key === simple_reconciler::subresource_configmap(cr_key).key
        }
    }
}

pub proof fn lemma_delete_cm_req_msg_never_in_flight(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(always(lift_state(delete_cm_req_msg_not_in_flight(cr_key)))),
{
    let invariant = delete_cm_req_msg_not_in_flight(cr_key);
    assert forall |s, s_prime: State<SimpleReconcileState>| invariant(s) && #[trigger] next(simple_reconciler())(s, s_prime) implies invariant(s_prime) by {
        assert(!exists |m: Message| s.message_in_flight(m)
            && m.dst === HostId::KubernetesAPI
            && #[trigger] m.is_delete_request()
            && m.get_delete_request().key === simple_reconciler::subresource_configmap(cr_key).key
        );
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);
}

}
