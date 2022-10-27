// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::map::*;
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

#[is_variant]
pub enum ResourceObj {
    CustomResource,
    StatefulSet,
    Pod,
    Volume,
}

#[is_variant]
pub enum ResourceKind {
    CustomResourceKind,
    StatefulSetKind,
    PodKind,
    VolumeKind,
}

#[is_variant]
pub enum Message {
    CreateRequest(CreateRequestMessage),
    CreateResponse(CreateResponseMessage),
}

pub struct CreateRequestMessage {
    pub name: Seq<char>,
    pub kind: ResourceKind,
    pub obj: ResourceObj,
}

pub struct CreateResponseMessage {
    pub name: Seq<char>,
    pub kind: ResourceKind,
}

pub struct CState {
    pub resources: Map<Seq<char>, ResourceObj>,
    pub messages: Set<Message>,
    // TODO: attached should be a field in Volume or Pod
    pub attached: Set<Seq<char>>,
}

/**
 *                  k8s_handle_create(cr)
 *                     /           \
 * controller_send_create_sts       controller_send_create_vol
 *                    |             |
 * k8s_handle_create(sts)           k8s_handle_create(vol)
 *                    |             |
 * k8s_handle_create(pod)           |
 *                    \             /
 *                     \           /
 *                 controller_attach_vol_to_pod
 *
 *
 * Note that this state machine is different from real controllers in several ways:
 * 1. Controllers usually issue sync call to k8s. It will only proceed after it
 * receives the response of the last call.
 * 2. Controllers' reconcile functions are usually single-threaded.
 * 3. Controllers don't and can't make decisions based on the sent messages.
 * Controllers rely on the response from the k8s and its local cache to make decision.
 * 4. In a real k8s cluster, the sts controller is supposed to create both the pod and vol
 * and attach the vol to the pod, rather than the custom controller.
 *
 */

pub open spec fn sts_suffix() -> Seq<char> {
    new_strlit("_sts")@
}

pub open spec fn pod_suffix() -> Seq<char> {
    new_strlit("_pod")@
}

pub open spec fn vol_suffix() -> Seq<char> {
    new_strlit("_vol")@
}

pub open spec fn message_sent(s: CState, m: Message) -> bool {
    s.messages.contains(m)
}

pub open spec fn resource_exists(s: CState, key: Seq<char>) -> bool {
    s.resources.dom().contains(key)
}

pub open spec fn create_cr_req_msg(name: Seq<char>) -> Message {
    Message::CreateRequest(CreateRequestMessage{
        name: name,
        kind: ResourceKind::CustomResourceKind,
        obj: ResourceObj::CustomResource,
    })
}

pub open spec fn create_sts_req_msg(name: Seq<char>) -> Message {
    Message::CreateRequest(CreateRequestMessage{
        name: name,
        kind: ResourceKind::StatefulSetKind,
        obj: ResourceObj::StatefulSet,
    })
}

pub open spec fn create_pod_req_msg(name: Seq<char>) -> Message {
    Message::CreateRequest(CreateRequestMessage{
        name: name,
        kind: ResourceKind::PodKind,
        obj: ResourceObj::Pod,
    })
}

pub open spec fn create_vol_req_msg(name: Seq<char>) -> Message {
    Message::CreateRequest(CreateRequestMessage{
        name: name,
        kind: ResourceKind::VolumeKind,
        obj: ResourceObj::Volume,
    })
}

pub open spec fn create_cr_resp_msg(name: Seq<char>) -> Message {
    Message::CreateResponse(CreateResponseMessage{
        name: name,
        kind: ResourceKind::CustomResourceKind,
    })
}

pub open spec fn create_pod_resp_msg(name: Seq<char>) -> Message {
    Message::CreateResponse(CreateResponseMessage{
        name: name,
        kind: ResourceKind::PodKind,
    })
}

pub open spec fn create_vol_resp_msg(name: Seq<char>) -> Message {
    Message::CreateResponse(CreateResponseMessage{
        name: name,
        kind: ResourceKind::VolumeKind,
    })
}

pub open spec fn create_resp_msg(name: Seq<char>, kind: ResourceKind) -> Message {
    Message::CreateResponse(CreateResponseMessage{
        name: name,
        kind: kind,
    })
}

pub open spec fn update_resources_with(s: CState, msg: CreateRequestMessage) -> Map<Seq<char>, ResourceObj> {
    if s.resources.dom().contains(msg.name) {
        s.resources
    } else {
        s.resources.insert(msg.name, msg.obj)
    }
}

pub open spec fn update_messages_with(s: CState, msg: CreateRequestMessage) -> Set<Message> {
    if msg.kind.is_StatefulSetKind() {
        // TODO: the number of pods created here should depend on the replica field in the sts
        s.messages.insert(create_resp_msg(msg.name, msg.kind)).insert(create_pod_req_msg(msg.name + pod_suffix()))
    } else {
        s.messages.insert(create_resp_msg(msg.name, msg.kind))
    }
}

pub open spec fn init() -> StatePred<CState> {
    |s: CState| {
        &&& s.resources === Map::empty()
        &&& s.messages === Set::empty()
        &&& s.attached === Set::empty()
    }
}

pub open spec fn controller_send_create_sts_pre(msg: Message) -> StatePred<CState> {
    |s| {
        &&& message_sent(s, msg)
        &&& msg.is_CreateResponse()
        &&& msg.get_CreateResponse_0().kind.is_CustomResourceKind()
    }
}

pub open spec fn controller_send_create_sts(msg: Message) -> ActionPred<CState> {
    |s, s_prime| {
        &&& controller_send_create_sts_pre(msg)(s)
        &&& s_prime === CState {
            messages: s.messages.insert(create_sts_req_msg(msg.get_CreateResponse_0().name + sts_suffix())),
            ..s
        }
    }
}

pub open spec fn controller_send_create_vol_pre(msg: Message) -> StatePred<CState> {
    |s| {
        &&& message_sent(s, msg)
        &&& msg.is_CreateResponse()
        &&& msg.get_CreateResponse_0().kind.is_CustomResourceKind()
    }
}

pub open spec fn controller_send_create_vol(msg: Message) -> ActionPred<CState> {
    |s, s_prime| {
        &&& controller_send_create_vol_pre(msg)(s)
        &&& s_prime === CState {
            messages: s.messages.insert(create_vol_req_msg(msg.get_CreateResponse_0().name + vol_suffix())),
            ..s
        }
    }
}

pub open spec fn k8s_handle_create_pre(msg: Message) -> StatePred<CState> {
    |s| {
        &&& message_sent(s, msg)
        &&& msg.is_CreateRequest()
    }
}

pub open spec fn k8s_handle_create(msg: Message) -> ActionPred<CState> {
    |s, s_prime| {
        &&& k8s_handle_create_pre(msg)(s)
        &&& s_prime === CState {
            resources: update_resources_with(s, msg.get_CreateRequest_0()),
            messages: update_messages_with(s, msg.get_CreateRequest_0()),
            ..s
        }
    }
}

/// This action is not realistic because actual controllers won't wait for two messages at the same time
/// A controller typically sends out a message, receives the response, and sends out another message...
pub open spec fn controller_attach_vol_to_pod_pre(cr_name: Seq<char>) -> StatePred<CState> {
    |s| {
        &&& message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
        &&& message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
    }
}

// TODO: controller_attach_vol_to_pod_pre should be parameterized by Message
// I didn't do so because it actually waits for two messages:
// One for pod creation and one for volume creation
// Not sure what is the best way to write actions that require receiving multiple messages
pub open spec fn controller_attach_vol_to_pod(cr_name: Seq<char>) -> ActionPred<CState> {
    |s, s_prime| {
        &&& controller_attach_vol_to_pod_pre(cr_name)(s)
        &&& s_prime === CState {
            attached: s.attached.insert(cr_name),
            ..s
        }
    }
}

pub open spec fn stutter() -> ActionPred<CState> {
    |s, s_prime| s === s_prime
}

pub enum ActionLabel {
    ControllerSendCreateSts(Message),
    ControllerSendCreateVol(Message),
    K8sHandleCreate(Message),
    K8sAttachVolToPod(Seq<char>),
    Stutter
}

pub open spec fn next_step(s: CState, s_prime: CState, action_label: ActionLabel) -> bool {
    match action_label {
        ActionLabel::ControllerSendCreateSts(msg) => controller_send_create_sts(msg)(s, s_prime),
        ActionLabel::ControllerSendCreateVol(msg) => controller_send_create_vol(msg)(s, s_prime),
        ActionLabel::K8sHandleCreate(msg) => k8s_handle_create(msg)(s, s_prime),
        ActionLabel::K8sAttachVolToPod(cr_name) => controller_attach_vol_to_pod(cr_name)(s, s_prime),
        ActionLabel::Stutter => stutter()(s, s_prime),
    }
}

pub open spec fn next() -> ActionPred<CState> {
    |s, s_prime| exists |action_label| next_step(s, s_prime, action_label)
}

pub open spec fn sm_spec() -> TempPred<CState> {
    lift_state(init())
    .and(always(lift_action(next())))
    .and(tla_forall(|msg| weak_fairness(controller_send_create_sts(msg))))
    .and(tla_forall(|msg| weak_fairness(controller_send_create_vol(msg))))
    .and(tla_forall(|msg| weak_fairness(k8s_handle_create(msg))))
    .and(tla_forall(|cr_name| weak_fairness(controller_attach_vol_to_pod(cr_name))))
}

pub proof fn controller_send_create_sts_enabled(msg: Message)
    ensures
        forall |s| state_pred_call(controller_send_create_sts_pre(msg), s)
            ==> enabled(controller_send_create_sts(msg))(s),
{
    assert forall |s| state_pred_call(controller_send_create_sts_pre(msg), s)
    implies enabled(controller_send_create_sts(msg))(s) by {
        let witness_s_prime = CState {
            messages: s.messages.insert(create_sts_req_msg(msg.get_CreateResponse_0().name + sts_suffix())),
            ..s
        };
        assert(action_pred_call(controller_send_create_sts(msg), s, witness_s_prime));
    };
}

pub proof fn controller_send_create_vol_enabled(msg: Message)
    ensures
        forall |s| state_pred_call(controller_send_create_vol_pre(msg), s)
            ==> enabled(controller_send_create_vol(msg))(s),
{
    assert forall |s| state_pred_call(controller_send_create_vol_pre(msg), s)
    implies enabled(controller_send_create_vol(msg))(s) by {
        let witness_s_prime = CState {
            messages: s.messages.insert(create_vol_req_msg(msg.get_CreateResponse_0().name + vol_suffix())),
            ..s
        };
        assert(action_pred_call(controller_send_create_vol(msg), s, witness_s_prime));
    };
}

pub proof fn k8s_handle_create_enabled(msg: Message)
    ensures
        forall |s| state_pred_call(k8s_handle_create_pre(msg), s)
            ==> enabled(k8s_handle_create(msg))(s),
{
    assert forall |s| state_pred_call(k8s_handle_create_pre(msg), s)
    implies enabled(k8s_handle_create(msg))(s) by {
        let witness_s_prime = CState {
            resources: update_resources_with(s, msg.get_CreateRequest_0()),
            messages: update_messages_with(s, msg.get_CreateRequest_0()),
            ..s
        };
        assert(action_pred_call(k8s_handle_create(msg), s, witness_s_prime));
    };
}

pub proof fn controller_attach_vol_to_pod_enabled(cr_name: Seq<char>)
    ensures
        forall |s| state_pred_call(controller_attach_vol_to_pod_pre(cr_name), s)
            ==> enabled(controller_attach_vol_to_pod(cr_name))(s),
{
    assert forall |s| state_pred_call(controller_attach_vol_to_pod_pre(cr_name), s)
    implies enabled(controller_attach_vol_to_pod(cr_name))(s) by {
        let witness_s_prime = CState {
            attached: s.attached.insert(cr_name),
            ..s
        };
        assert(action_pred_call(controller_attach_vol_to_pod(cr_name), s, witness_s_prime));
    };
}

}
