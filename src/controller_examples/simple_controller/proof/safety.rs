// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_examples::simple_controller::proof::shared::*;
use crate::controller_examples::simple_controller::spec::{
    custom_resource::*,
    reconciler,
    reconciler::{simple_reconciler, SimpleReconcileState},
};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, object_meta::ObjectMetaView, resource::*,
};
use crate::kubernetes_cluster::{
    proof::{
        controller_runtime_liveness::reconciler_init_and_no_pending_req, controller_runtime_safety,
        kubernetes_api_safety,
    },
    spec::{
        controller::common::{controller_req_msg, ControllerAction, ControllerActionInput},
        distributed_system::*,
        kubernetes_api::state_machine::handle_get_request,
        message::*,
    },
};
use crate::temporal_logic::{defs::*, rules::*};
use builtin::*;
use builtin_macros::*;
use vstd::{option::*, result::*};

verus! {

pub proof fn lemma_always_reconcile_init_pc_and_no_pending_req(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(reconciler_at_init_pc(cr)).implies(lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref())))
        )),
{
    let invariant = |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr.object_ref())
        && s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::init_pc()
        ==> s.reconcile_state_contains(cr.object_ref())
            && s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::init_pc()
            && s.reconcile_state_of(cr.object_ref()).pending_req_msg.is_None()
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    // We intentionally write the safety property in a form that is friendly to liveness reasoning
    // There is no need to do this if we only want to prove safety
    let invariant_temp_pred = lift_state(reconciler_at_init_pc(cr)).implies(lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref())));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(invariant), invariant_temp_pred);
}

pub open spec fn reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr.object_ref())
        && s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_get_cr_pc()
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

    controller_runtime_safety::lemma_always_each_resp_matches_at_most_one_pending_req(simple_reconciler(), cr.object_ref());

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
    if s_prime.reconcile_state_contains(cr.object_ref()) && s_prime.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_get_cr_pc() {
        // Depending on whether reconcile state is at after_get_cr_pc, we need to reason about different transitions
        if s.reconcile_state_contains(cr.object_ref()) && s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_get_cr_pc() {
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
            let req_msg = controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr.object_ref()}), s.chan_manager.cur_chan_id);
            assert(is_controller_get_cr_request_msg(req_msg, cr)
                && s_prime.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg)
                && s_prime.message_in_flight(req_msg)
            ); // providing witness for exists |req_msg| ...
        }
    }
}

pub open spec fn metadata_with_same_name_and_namespace(metadata1: ObjectMetaView, metadata2: ObjectMetaView) -> bool {
    metadata1.name == metadata2.name && metadata1.namespace == metadata2.namespace
}

pub open spec fn matched_in_flight_resp_msg_has_same_metadata_as_cr(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        forall |resp_msg: Message|
            s.reconcile_state_contains(cr.object_ref())
            && s.reconcile_state_of(cr.object_ref()).pending_req_msg.is_Some()
            && #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(cr.object_ref()).pending_req_msg.get_Some_0())
            && resp_msg.content.get_APIResponse_0().is_GetResponse()
            && resp_msg.content.get_APIResponse_0().get_GetResponse_0().res.is_Ok()
            ==> metadata_with_same_name_and_namespace(cr.metadata, resp_msg.content.get_APIResponse_0().get_GetResponse_0().res.get_Ok_0().metadata)
    }
}

pub proof fn lemma_always_matched_in_flight_resp_msg_has_same_metadata_as_cr(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(always(lift_state(matched_in_flight_resp_msg_has_same_metadata_as_cr(cr)))),
{
    let invariant = matched_in_flight_resp_msg_has_same_metadata_as_cr(cr);

    let stronger_next = |s, s_prime: State<SimpleReconcileState>| {
        next(simple_reconciler())(s, s_prime)
        && controller_runtime_safety::every_in_flight_msg_has_unique_id::<SimpleReconcileState>()(s)
        && controller_runtime_safety::every_in_flight_or_pending_req_has_unique_id::<SimpleReconcileState>(cr.object_ref())(s)
        && controller_runtime_safety::every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>()(s)
    };

    controller_runtime_safety::lemma_always_every_in_flight_msg_has_unique_id::<CustomResourceView, SimpleReconcileState>(simple_reconciler());
    controller_runtime_safety::lemma_always_every_in_flight_or_pending_req_has_unique_id::<CustomResourceView, SimpleReconcileState>(simple_reconciler(), cr.object_ref());
    controller_runtime_safety::lemma_always_every_in_flight_msg_has_lower_id_than_chan_manager::<CustomResourceView, SimpleReconcileState>(simple_reconciler());

    // make strengthen next inline here because we don't have the two-inv version :-(
    entails_and_n!(sm_spec(simple_reconciler()), always(lift_action(next(simple_reconciler()))), always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id::<SimpleReconcileState>())), always(lift_state(controller_runtime_safety::every_in_flight_or_pending_req_has_unique_id::<SimpleReconcileState>(cr.object_ref()))), always(lift_state(controller_runtime_safety::every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>())));

    entails_always_and_n!(sm_spec(simple_reconciler()), lift_action(next(simple_reconciler())), lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id::<SimpleReconcileState>()), lift_state(controller_runtime_safety::every_in_flight_or_pending_req_has_unique_id::<SimpleReconcileState>(cr.object_ref())), lift_state(controller_runtime_safety::every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>()));

    temp_pred_equality(lift_action(stronger_next), lift_action(next(simple_reconciler())).and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id::<SimpleReconcileState>())).and(lift_state(controller_runtime_safety::every_in_flight_or_pending_req_has_unique_id::<SimpleReconcileState>(cr.object_ref()))).and(lift_state(controller_runtime_safety::every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>())));

    assert forall |s, s_prime: State<SimpleReconcileState>| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |resp_msg: Message| s_prime.reconcile_state_contains(cr.object_ref())
        && s_prime.message_in_flight(resp_msg) && s_prime.reconcile_state_of(cr.object_ref()).pending_req_msg.is_Some() && #[trigger] resp_msg_matches_req_msg(resp_msg, s_prime.reconcile_state_of(cr.object_ref()).pending_req_msg.get_Some_0()) && resp_msg.content.get_APIResponse_0().is_GetResponse() && resp_msg.content.get_APIResponse_0().get_GetResponse_0().res.is_Ok()
        implies metadata_with_same_name_and_namespace(cr.metadata, resp_msg.content.get_APIResponse_0().get_GetResponse_0().res.get_Ok_0().metadata) by {
            let next_step = choose |step: Step<CustomResourceView>| next_step(simple_reconciler(), s, s_prime, step);
            match next_step {
                Step::KubernetesAPIStep(input) => {
                    assert(s.reconcile_state_of(cr.object_ref()).pending_req_msg == s_prime.reconcile_state_of(cr.object_ref()).pending_req_msg);
                    let pending_req = s.reconcile_state_of(cr.object_ref()).pending_req_msg.get_Some_0();
                    // pending_req doesn't change
                    if (s.message_in_flight(resp_msg)) {
                        assert(metadata_with_same_name_and_namespace(cr.metadata, resp_msg.content.get_APIResponse_0().get_GetResponse_0().res.get_Ok_0().metadata));
                    } else {
                        assert(s.reconcile_state_contains(cr.object_ref()));
                        assume((input.get_Some_0() == pending_req) ==> cr.metadata == resp_msg.content.get_APIResponse_0().get_GetResponse_0().res.get_Ok_0().metadata);
                        assert(input.get_Some_0() == pending_req);
                        // assert(pending_req.content.get_get_request().key == cr.object_ref());
                        assert(metadata_with_same_name_and_namespace(cr.metadata, resp_msg.content.get_APIResponse_0().get_GetResponse_0().res.get_Ok_0().metadata));
                    }
                }
                Step::ControllerStep(input) => {
                    assert(s.message_in_flight(resp_msg));
                    assert(resp_msg.content.get_resp_id() < s.chan_manager.cur_chan_id);
                    if input.1.get_Some_0() == cr.object_ref() {
                        assert(s_prime.reconcile_state_of(cr.object_ref()).pending_req_msg.get_Some_0().content.get_req_id() == s.chan_manager.cur_chan_id);
                        assert(false);
                    }
                    else {
                        assert(metadata_with_same_name_and_namespace(cr.metadata, resp_msg.content.get_APIResponse_0().get_GetResponse_0().res.get_Ok_0().metadata));
                    }
                }
                Step::ClientStep(input) => {
                    assert(s.reconcile_state_contains(cr.object_ref()));
                    assert(s.reconcile_state_of(cr.object_ref()) == s_prime.reconcile_state_of(cr.object_ref()));
                    assert(s.message_in_flight(resp_msg));
                }
                _ => {
                    assert(metadata_with_same_name_and_namespace(cr.metadata, resp_msg.content.get_APIResponse_0().get_GetResponse_0().res.get_Ok_0().metadata));
                }
            }
        };
    };

    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()),
        stronger_next, invariant);
}

pub open spec fn delete_cm_req_msg_not_in_flight(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        !exists |m: Message| {
            &&& #[trigger] s.message_in_flight(m)
            &&& m.dst == HostId::KubernetesAPI
            &&& m.content.is_delete_request()
            &&& m.content.get_delete_request().key == reconciler::subresource_configmap(cr).object_ref()
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
            && m.content.get_delete_request().key == reconciler::subresource_configmap(cr).object_ref()
        );
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);
}

}
