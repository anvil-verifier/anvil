// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{
    common::*,
    controller::common::{controller_req_msg, ControllerAction, ControllerActionInput},
    distributed_system::*,
};
use crate::pervasive::*;
use crate::pervasive::{option::*, result::*};
use crate::simple_controller::spec::{
    simple_reconciler,
    simple_reconciler::{simple_reconciler, SimpleReconcileState},
};
use builtin::*;
use builtin_macros::*;

verus! {

pub closed spec fn dummy_trigger<A>(x: A);

pub open spec fn is_controller_get_cr_request_msg(msg: Message, cr_key: ResourceKey) -> bool {
    &&& msg.src === HostId::CustomController
    &&& msg.dst === HostId::KubernetesAPI
    &&& msg.is_get_request()
    &&& msg.get_get_request().key === cr_key
}

pub open spec fn is_controller_create_cm_request_msg(msg: Message, cr_key: ResourceKey) -> bool {
    &&& msg.src === HostId::CustomController
    &&& msg.dst === HostId::KubernetesAPI
    &&& msg.is_create_request()
    &&& msg.get_create_request().obj === simple_reconciler::subresource_configmap(cr_key)
    // === simple_reconciler::create_cm_req(cr_key)
}

pub type ChosenMessage = FnSpec(State<SimpleReconcileState>) -> Message;

pub open spec fn choose_pending_controller_get_cr_request_msg(cr_key: ResourceKey) -> ChosenMessage {
    |s: State<SimpleReconcileState>| {
        choose |m| {
            &&& is_controller_get_cr_request_msg(m, cr_key)
            &&& #[trigger] s.message_sent(m)
            &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(m)
        }
    }
}

}
