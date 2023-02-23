// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{
    common::*,
    controller::common::{controller_req_msg, ControllerAction, ControllerActionInput},
    distributed_system::*,
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
            lift_state(reconciler_at_init_pc(cr_key))
            .implies(lift_state(|s: State<SimpleReconcileState>| {
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
    let invariant_temp_pred = lift_state(reconciler_at_init_pc(cr_key))
    .implies(lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    }));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(invariant), invariant_temp_pred);
}


pub proof fn lemma_always_reconcile_get_cr_done_implies_pending_get_cr_req(cr_key: ResourceKey) -> (inv: TempPred<State<SimpleReconcileState>>)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        inv === lift_state(reconciler_at_after_get_cr_pc(cr_key))
        .implies(lift_state(|s: State<SimpleReconcileState>| {
            exists |m| {
                &&& is_controller_get_cr_request_msg(m, cr_key)
                &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
                &&& #[trigger] s.message_in_flight(m)
            }
        })),
        sm_spec(simple_reconciler()).entails(always(inv)),
{
    let invariant = |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        ==> exists |m| {
                is_controller_get_cr_request_msg(m, cr_key)
                && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
                && #[trigger] s.message_in_flight(m)
            }
    };

    assert forall |s, s_prime: State<SimpleReconcileState>| invariant(s) && #[trigger] next(simple_reconciler())(s, s_prime) implies invariant(s_prime) by {
        if s.reconcile_state_contains(cr_key) && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc() {
            if s_prime.reconcile_state_contains(cr_key) && s_prime.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc() {
                let m = choose |m| is_controller_get_cr_request_msg(m, cr_key)
                    && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
                    && #[trigger] s.message_in_flight(m);
                assert(is_controller_get_cr_request_msg(m, cr_key)
                    && s_prime.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
                    && s_prime.message_in_flight(m)
                );
            }
        } else {
            if s_prime.reconcile_state_contains(cr_key) && s_prime.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc() {
                let m = controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key}), s.controller_state.req_id);
                assert(is_controller_get_cr_request_msg(m, cr_key)
                    && s_prime.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
                    && s_prime.message_in_flight(m)
                );
            }
        }
    };

    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    let invariant_temp_pred = lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
    }).implies(lift_state(|s: State<SimpleReconcileState>| {
        exists |m| {
            &&& is_controller_get_cr_request_msg(m, cr_key)
            &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
            &&& #[trigger] s.message_in_flight(m)
        }
    }));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(invariant), invariant_temp_pred);

    invariant_temp_pred
}

pub proof fn lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req(cr_key: ResourceKey) -> (inv: TempPred<State<SimpleReconcileState>>)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        inv === lift_state(reconciler_at_after_create_cm_pc(cr_key))
        .implies(lift_state(|s: State<SimpleReconcileState>| {
            exists |m| {
                &&& is_controller_create_cm_request_msg(m, cr_key)
                &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
                &&& #[trigger] s.message_in_flight(m)
            }
        })),
        sm_spec(simple_reconciler()).entails(always(inv)),
{
    let invariant = |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr_key) && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
        ==> exists |m| {
                is_controller_create_cm_request_msg(m, cr_key)
                && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
                && #[trigger] s.message_in_flight(m)
            }
    };

    assert forall |s, s_prime: State<SimpleReconcileState>| invariant(s) && #[trigger] next(simple_reconciler())(s, s_prime) implies invariant(s_prime) by {
        if s.reconcile_state_contains(cr_key) && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc() {
            if s_prime.reconcile_state_contains(cr_key) && s_prime.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc() {
                let m = choose |m| is_controller_create_cm_request_msg(m, cr_key)
                    && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
                    && #[trigger] s.message_in_flight(m);
                assert(is_controller_create_cm_request_msg(m, cr_key)
                    && s_prime.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
                    && s_prime.message_in_flight(m)
                );
            }
        } else {
            if s_prime.reconcile_state_contains(cr_key) && s_prime.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc() {
                let m = controller_req_msg(simple_reconciler::create_cm_req(cr_key), s.controller_state.req_id);
                assert(is_controller_create_cm_request_msg(m, cr_key)
                    && s_prime.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
                    && s_prime.message_in_flight(m)
                );
            }
        }
    };

    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    let invariant_temp_pred = lift_state(reconciler_at_after_create_cm_pc(cr_key))
    .implies(lift_state(|s: State<SimpleReconcileState>| {
        exists |m| {
            &&& is_controller_create_cm_request_msg(m, cr_key)
            &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
            &&& #[trigger] s.message_in_flight(m)
        }
    }));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(invariant), invariant_temp_pred);

    invariant_temp_pred
}

pub proof fn lemma_delete_cm_req_msg_never_sent(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(|s: State<SimpleReconcileState>| !exists |m: Message| {
                &&& #[trigger] s.message_in_flight(m)
                &&& m.dst === HostId::KubernetesAPI
                &&& m.is_delete_request()
                &&& m.get_delete_request().key === simple_reconciler::subresource_configmap(cr_key).key
            })
        )),
{
    let invariant = |s: State<SimpleReconcileState>| !exists |m: Message| {
        &&& #[trigger] s.message_in_flight(m)
        &&& m.dst === HostId::KubernetesAPI
        &&& m.is_delete_request()
        &&& m.get_delete_request().key === simple_reconciler::subresource_configmap(cr_key).key
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);
}

}
