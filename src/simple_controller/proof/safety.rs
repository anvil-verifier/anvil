// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, custom_resource::*, object::*,
};
use crate::kubernetes_cluster::{
    proof::{controller_runtime_safety, kubernetes_api_safety},
    spec::{
        controller::common::{controller_req_msg, ControllerAction, ControllerActionInput},
        distributed_system::*,
        kubernetes_api::state_machine::handle_get_request,
        message::*,
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

pub open spec fn reconcile_init_pc_and_no_pending_req(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::init_pc()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg.is_None()
    }
}

pub proof fn lemma_always_reconcile_init_pc_and_no_pending_req(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(reconciler_at_init_pc(cr)).implies(lift_state(reconcile_init_pc_and_no_pending_req(cr)))
        )),
{
    let invariant = |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr.object_ref())
        && s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::init_pc()
        ==> s.reconcile_state_contains(cr.object_ref())
            && s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::init_pc()
            && s.reconcile_state_of(cr.object_ref()).pending_req_msg.is_None()
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    // We intentionally write the safety property in a form that is friendly to liveness reasoning
    // There is no need to do this if we only want to prove safety
    let invariant_temp_pred = lift_state(reconciler_at_init_pc(cr)).implies(lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::init_pc()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg.is_None()
    }));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(invariant), invariant_temp_pred);
}

pub open spec fn reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr.object_ref())
        && s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_get_cr_pc()
        ==> exists |req_msg| {
                #[trigger] is_controller_get_cr_request_msg(req_msg, cr)
                && s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg)
                && (s.message_in_flight(req_msg)
                    || exists |resp_msg: Message| {
                        #[trigger] s.message_in_flight(resp_msg)
                        && resp_msg_matches_req_msg(resp_msg, req_msg)
                    })
            }
    }
}

/// If the reconcile is at get_cr_done_pc, then (1) a get cr request message is sent or (2) the corresponding response is sent.
pub proof fn lemma_always_reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(always(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr)))),
{
    let invariant = reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr);

    let stronger_next = |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(cr.object_ref())(s)
    };

    assert forall |s, s_prime: State<SimpleReconcileState>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        next_preserves_reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr, s, s_prime);
    };

    controller_runtime_safety::lemma_always_each_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(simple_reconciler(), cr.object_ref());

    strengthen_next::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), controller_runtime_safety::each_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(cr.object_ref()), stronger_next);
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), stronger_next, invariant);
}

// next (and each_resp_matches_at_most_one_pending_req) preserves reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight
proof fn next_preserves_reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr: CustomResourceView, s: State<SimpleReconcileState>, s_prime: State<SimpleReconcileState>)
    requires
        reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr)(s),
        controller_runtime_safety::each_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(cr.object_ref())(s),
        next(simple_reconciler())(s, s_prime),
    ensures
        reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr)(s_prime),
{
    // We only care about the case where reconcile state is at after_get_cr_pc at s_prime
    if s_prime.reconcile_state_contains(cr.object_ref()) && s_prime.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_get_cr_pc() {
        // Depending on whether reconcile state is at after_get_cr_pc, we need to reason about different transitions
        if s.reconcile_state_contains(cr.object_ref()) && s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_get_cr_pc() {
            let req_msg = choose |req_msg| #[trigger] is_controller_get_cr_request_msg(req_msg, cr) && s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg);
            assert(is_controller_get_cr_request_msg(req_msg, cr) && s_prime.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg));
            // If req_msg is in flight at s...
            if s.message_in_flight(req_msg) {
                // ... then either (1) the req_msg is still in flight at s_prime, or (2) req_msg is handled by k8s and the resp is in flight
                if s_prime.message_in_flight(req_msg) {
                    assert(s_prime.message_in_flight(req_msg)); // providing witness for exists |req_msg| ...
                } else {
                    let (_, resp_msg, _) = handle_get_request(req_msg, s.kubernetes_api_state);
                    assert(s_prime.message_in_flight(resp_msg) && resp_msg_matches_req_msg(resp_msg, req_msg)); // providing witness for exists |resp_msg| ...
                }
            } else {
                // If req_msg is not in flight at s, then the corresponding resp_msg is in flight at s
                let resp_msg = choose |resp_msg| #[trigger] s.message_in_flight(resp_msg) && resp_msg_matches_req_msg(resp_msg, req_msg);
                // The key here is to use the safety invariant: resp_matches_at_most_one_pending_req
                // It says each response message can match only one pending request message, so req_msg is the only message that can match resp_msg
                // In other words, if resp_msg is delivered to the controller in this transition, then the reconcile state of cr.object_ref() will be advanced to the next pc at s_prime
                // By contraposition, since the reconcile state is still after_get_cr_pc at s_prime, we can show that resp_msg is still in flight in s_prime
                assert(controller_runtime_safety::resp_matches_at_most_one_pending_req::<SimpleReconcileState>(resp_msg, cr.object_ref())(s));
                assert(s_prime.message_in_flight(resp_msg) && resp_msg_matches_req_msg(resp_msg, req_msg)); // providing witness for exists |resp_msg| ...
            }
        } else {
            // If reconcile state is not at after_get_cr_pc for s, then this in transition reconcile_core advances the reconcile state to after_get_cr_pc
            // which means the req_msg is just sent to the network, so of course it is in flight
            let req_msg = controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr.object_ref()}), s.controller_state.chan_manager.cur_chan_id);
            assert(is_controller_get_cr_request_msg(req_msg, cr)
                && s_prime.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg)
                && s_prime.message_in_flight(req_msg)
            ); // providing witness for exists |req_msg| ...
        }
    }
}

pub open spec fn reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr.object_ref())
        && s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_create_cm_pc()
        ==> exists |req_msg| {
                #[trigger] is_controller_create_cm_request_msg(req_msg, cr)
                && s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg)
                && (s.message_in_flight(req_msg) || s.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref()))
            }
    }
}

/// If the reconcile is at create_cm_done_pc, then (1) a create cm request message is sent or (2) the corresponding response is sent.
pub proof fn lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr)))),
{
    let invariant = reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr);

    let stronger_next = |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& delete_cm_req_msg_not_in_flight(cr)(s)
    };

    assert forall |s, s_prime: State<SimpleReconcileState>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        next_preserves_reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr, s, s_prime);
    };

    lemma_delete_cm_req_msg_never_in_flight(cr);

    strengthen_next::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), delete_cm_req_msg_not_in_flight(cr), stronger_next);
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), stronger_next, invariant);
}

proof fn next_preserves_reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr: CustomResourceView, s: State<SimpleReconcileState>, s_prime: State<SimpleReconcileState>)
    requires
        reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr)(s),
        delete_cm_req_msg_not_in_flight(cr)(s),
        next(simple_reconciler())(s, s_prime),
    ensures
        reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr)(s_prime),
{
    if s_prime.reconcile_state_contains(cr.object_ref()) && s_prime.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_create_cm_pc() {
        if s.reconcile_state_contains(cr.object_ref()) && s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_create_cm_pc() {
            let req_msg = choose |req_msg| #[trigger] is_controller_create_cm_request_msg(req_msg, cr) && s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg);
            assert(is_controller_create_cm_request_msg(req_msg, cr) && s_prime.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg));
            if s.message_in_flight(req_msg) {
                if s.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref()) {
                    assert(s_prime.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref()));
                } else {
                    if s_prime.message_in_flight(req_msg) {
                        assert(s_prime.message_in_flight(req_msg));
                    } else {
                        assert(s_prime.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref()));
                    }
                }
            } else {
                assert(s_prime.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref()));
            }
        } else {
            let req_msg = controller_req_msg(simple_reconciler::create_cm_req(cr.object_ref()), s.controller_state.chan_manager.cur_chan_id);
            assert(is_controller_create_cm_request_msg(req_msg, cr)
                && s_prime.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg)
                && s_prime.message_in_flight(req_msg)
            );
        }
    }
}

pub open spec fn delete_cm_req_msg_not_in_flight(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        !exists |m: Message| {
            &&& #[trigger] s.message_in_flight(m)
            &&& m.dst == HostId::KubernetesAPI
            &&& m.content.is_delete_request()
            &&& m.content.get_delete_request().key == simple_reconciler::subresource_configmap(cr.object_ref()).object_ref()
        }
    }
}

pub proof fn lemma_delete_cm_req_msg_never_in_flight(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(always(lift_state(delete_cm_req_msg_not_in_flight(cr)))),
{
    let invariant = delete_cm_req_msg_not_in_flight(cr);
    assert forall |s, s_prime: State<SimpleReconcileState>| invariant(s) && #[trigger] next(simple_reconciler())(s, s_prime) implies invariant(s_prime) by {
        assert(!exists |m: Message| s.message_in_flight(m)
            && m.dst == HostId::KubernetesAPI
            && #[trigger] m.content.is_delete_request()
            && m.content.get_delete_request().key == simple_reconciler::subresource_configmap(cr.object_ref()).object_ref()
        );
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);
}

}
