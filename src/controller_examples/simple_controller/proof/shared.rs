// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_examples::simple_controller::spec::{
    reconciler,
    reconciler::{simple_reconciler, SimpleReconcileState},
};
use crate::kubernetes_api_objects::{common::*, config_map::*, custom_resource::*};
use crate::kubernetes_cluster::spec::{
    controller::common::{controller_req_msg, ControllerAction, ControllerActionInput},
    distributed_system::*,
    message::*,
};
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::*;
use vstd::{option::*, result::*};

verus! {

pub closed spec fn dummy_trigger<A>(x: A);

pub open spec fn reconciler_at_init_pc(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::init_pc()
    }
}

pub open spec fn reconciler_at_init_pc_and_no_pending_req(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::init_pc()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg.is_None()
    }
}

pub open spec fn reconciler_at_after_get_cr_pc(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_get_cr_pc()
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req(msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(msg)
        &&& is_controller_get_cr_request_msg(msg, cr)
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_ok_resp_in_flight(req_msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& is_controller_get_cr_request_msg(req_msg, cr)
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg)
        &&& s.message_in_flight(form_get_resp_msg(req_msg, Result::Ok(cr.to_dynamic_object())))
        
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& exists |req_msg| {
            &&& #[trigger] is_controller_get_cr_request_msg(req_msg, cr)
            &&& s.message_in_flight(req_msg)
            &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg)
            &&& (! exists |resp_msg: Message| 
                #![trigger s.message_in_flight(resp_msg)]
                #![trigger resp_msg_matches_req_msg(resp_msg, req_msg)]
                s.message_in_flight(resp_msg)
                && resp_msg_matches_req_msg(resp_msg, req_msg))
        }
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req_in_flight_and_no_resp_in_flight(req_msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg)
        &&& is_controller_get_cr_request_msg(req_msg, cr)
        &&& s.message_in_flight(req_msg)
        &&& ! exists |resp_msg: Message| {
            &&& s.message_in_flight(resp_msg)
            &&& #[trigger] resp_msg_matches_req_msg(resp_msg, req_msg)
        }
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(msg)
        &&& is_controller_get_cr_request_msg(msg, cr)
        &&& s.message_in_flight(msg)
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req_and_resp_in_flight(msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_get_cr_pc()
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
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_create_cm_pc()
    }
}

pub open spec fn reconciler_at_after_create_cm_pc_and_pending_req_and_req_in_flight(msg: Message, cr: CustomResourceView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state.reconcile_pc == reconciler::after_create_cm_pc()
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
    |s: State<SimpleReconcileState>| s.resource_key_exists(reconciler::subresource_configmap(cr.object_ref()).object_ref())
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
    &&& msg.content.get_create_request().obj == reconciler::subresource_configmap(cr.object_ref()).to_dynamic_object()
}

}
