// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, config_map::*, custom_resource::*, object::*};
use crate::kubernetes_cluster::spec::{
    controller::common::{controller_req_msg, ControllerAction, ControllerActionInput},
    distributed_system::*,
    message::*,
};
use crate::pervasive::*;
use crate::pervasive::{option::*, result::*};
use crate::simple_controller::spec::{
    simple_reconciler,
    simple_reconciler::{simple_reconciler, SimpleReconcileState},
};
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub closed spec fn dummy_trigger<A>(x: A);

pub open spec fn reconciler_at_init_pc(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::init_pc()
    }
}

pub open spec fn reconciler_at_init_pc_and_no_pending_req(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::init_pc()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg.is_None()
    }
}

pub open spec fn reconciler_at_after_get_cr_pc(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_get_cr_pc()
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req(msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(msg)
        &&& is_controller_get_cr_request_msg(msg, cr)
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(msg)
        &&& is_controller_get_cr_request_msg(msg, cr)
        &&& s.message_in_flight(msg)
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req_and_resp_in_flight(msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(msg)
        &&& is_controller_get_cr_request_msg(msg, cr)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
        }
    }
}


pub open spec fn get_cr_req_in_flight(msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& is_controller_get_cr_request_msg(msg, cr)
        &&& s.message_in_flight(msg)
    }
}

pub open spec fn reconciler_at_after_create_cm_pc(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_create_cm_pc()
    }
}

pub open spec fn reconciler_at_after_create_cm_pc_and_pending_req_and_req_in_flight(msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == simple_reconciler::after_create_cm_pc()
        &&& is_controller_create_cm_request_msg(msg, cr)
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(msg)
        &&& s.message_in_flight(msg)
    }
}

pub open spec fn reconciler_reconcile_done(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& (simple_reconciler().reconcile_done)(s.reconcile_state_of(cr.object_ref()).local_state)
    }
}

pub open spec fn reconciler_reconcile_error(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& (simple_reconciler().reconcile_error)(s.reconcile_state_of(cr.object_ref()).local_state)
    }
}

pub open spec fn cm_exists(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref())
}

pub open spec fn is_controller_get_cr_request_msg(msg: Message, cr: CustomResourceView) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_get_request()
    &&& msg.content.get_get_request().key == cr.object_ref()
}

pub open spec fn is_controller_create_cm_request_msg(msg: Message, cr: CustomResourceView) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_create_request()
    &&& msg.content.get_create_request().obj == KubernetesObject::ConfigMap(simple_reconciler::subresource_configmap(cr.object_ref()))
}

}
