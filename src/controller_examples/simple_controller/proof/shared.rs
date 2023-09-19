// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, config_map::*, resource::*};
use crate::kubernetes_cluster::spec::{
    controller::common::{controller_req_msg, ControllerAction, ControllerActionInput},
    cluster::*,
    message::*,
};
use crate::simple_controller::spec::*;
use crate::simple_controller::spec::{
    custom_resource::*,
    reconciler,
    reconciler::{simple_reconciler, SimpleReconcileState},
};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub type SimpleMessage = Message<EmptyTypeView, EmptyTypeView>;

pub closed spec fn dummy_trigger<A>(x: A);

pub open spec fn reconciler_at_init_pc(cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == SimpleReconcileStep::Init)
    }
}

pub open spec fn reconciler_at_init_pc_and_no_pending_req(cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == SimpleReconcileStep::Init)
        &&& no_pending_req_msg_or_external_api_input(s, cr.object_ref())
    }
}

pub open spec fn reconciler_at_after_get_cr_pc(cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == reconciler::after_get_cr_pc()
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req(msg: SimpleMessage, cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& pending_k8s_api_req_msg_is(s, cr.object_ref(), msg)
        &&& is_controller_get_cr_request_msg(msg, cr)
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_ok_resp_with_name_and_namespace_in_flight(req_msg: SimpleMessage, cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& is_controller_get_cr_request_msg(req_msg, cr)
        &&& s.ongoing_reconciles()[cr.object_ref()].pending_req_msg == Some(req_msg)
        &&& s.in_flight().contains(Message::form_get_resp_msg(req_msg, Ok(cr.marshal())))
        &&& (cr.metadata.name.is_Some() && cr.metadata.namespace.is_Some())
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& exists |req_msg| {
            &&& #[trigger] is_controller_get_cr_request_msg(req_msg, cr)
            &&& s.in_flight().contains(req_msg)
            &&& s.ongoing_reconciles()[cr.object_ref()].pending_req_msg == Some(req_msg)
            &&& (! exists |resp_msg: SimpleMessage|
                #![trigger s.in_flight().contains(resp_msg)]
                #![trigger resp_msg_matches_req_msg(resp_msg, req_msg)]
                s.in_flight().contains(resp_msg)
                && Message::resp_msg_matches_req_msg(resp_msg, req_msg))
        }
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req_in_flight_and_no_resp_in_flight(req_msg: SimpleMessage, cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& s.ongoing_reconciles()[cr.object_ref()].pending_req_msg == Some(req_msg)
        &&& is_controller_get_cr_request_msg(req_msg, cr)
        &&& s.in_flight().contains(req_msg)
        &&& ! exists |resp_msg: SimpleMessage| {
            &&& s.in_flight().contains(resp_msg)
            &&& #[trigger] Message::resp_msg_matches_req_msg(resp_msg, req_msg)
        }
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(msg: SimpleMessage, cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& s.ongoing_reconciles()[cr.object_ref()].pending_req_msg == Some(msg)
        &&& is_controller_get_cr_request_msg(msg, cr)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req_and_exists_resp_in_flight(msg: SimpleMessage, cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& s.ongoing_reconciles()[cr.object_ref()].pending_req_msg == Some(msg)
        &&& is_controller_get_cr_request_msg(msg, cr)
        &&& exists |resp_msg: SimpleMessage| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        }
    }
}

pub open spec fn reconciler_at_after_get_cr_pc_and_pending_req_and_resp_in_flight(req_msg: SimpleMessage, resp_msg: SimpleMessage, cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == reconciler::after_get_cr_pc()
        &&& s.ongoing_reconciles()[cr.object_ref()].pending_req_msg == Some(req_msg)
        &&& is_controller_get_cr_request_msg(req_msg, cr)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
    }
}

pub open spec fn reconciler_at_after_create_cm_pc_and_req_in_flight_and_cm_created(cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        reconciler_at_after_create_cm_pc(cr)(s)
        && exists |req_msg: SimpleMessage|
            #![trigger s.in_flight().contains(req_msg)]
            #![trigger req_msg.content.is_create_request()]
            s.in_flight().contains(req_msg)
            && req_msg.dst == HostId::KubernetesAPI
            && req_msg.content.is_create_request()
            && req_msg.content.get_create_request().obj == reconciler::make_config_map(cr).marshal()
    }
}

pub open spec fn reconciler_at_after_create_cm_pc(cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& s.ongoing_reconciles()[cr.object_ref()].local_state.reconcile_pc == reconciler::after_create_cm_pc()
    }
}

pub open spec fn reconciler_reconcile_done(cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& simple_reconciler().reconcile_done(s.ongoing_reconciles()[cr.object_ref()].local_state)
    }
}

pub open spec fn reconciler_reconcile_error(cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        &&& s.ongoing_reconciles().contains_key(cr.object_ref())
        &&& simple_reconciler().reconcile_error(s.ongoing_reconciles()[cr.object_ref()].local_state)
    }
}

pub open spec fn reconciler_reconcile_done_or_error(cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| {
        s.ongoing_reconciles().contains_key(cr.object_ref())
        && (simple_reconciler().reconcile_done(s.ongoing_reconciles()[cr.object_ref()].local_state) ||
        simple_reconciler().reconcile_error(s.ongoing_reconciles()[cr.object_ref()].local_state))
    }
}

pub open spec fn cm_exists(cr: SimpleCRView) -> StatePred<State<SimpleReconcileState>> {
    |s: State<SimpleReconcileState>| s.resources().contains_key(reconciler::make_config_map(cr).object_ref())
}

pub open spec fn is_controller_get_cr_request_msg(msg: SimpleMessage, cr: SimpleCRView) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_get_request()
    &&& msg.content.get_get_request().key == cr.object_ref()
}

pub open spec fn is_controller_create_cm_request_msg(msg: SimpleMessage, cr: SimpleCRView) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_create_request()
    &&& msg.content.get_create_request().obj == reconciler::make_config_map(cr).marshal()
}

}
