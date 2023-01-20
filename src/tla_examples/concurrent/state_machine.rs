// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::map::*;
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
use crate::pervasive::string::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

// #[is_variant]
// pub enum ResourceObj {
//     CustomResource,
//     StatefulSet,
//     Pod,
//     Volume,
// }

#[is_variant]
pub enum ResourceKind {
    CustomResourceKind,
    StatefulSetKind,
    PodKind,
    VolumeKind,
}

pub struct ResourceKey {
    pub name: Seq<char>,
    pub kind: ResourceKind,
}

/// TODO: change it back to enum when working on Update request
pub struct ResourceObj {
    pub key: ResourceKey,
}

#[is_variant]
pub enum Message {
    CreateRequest(CreateRequest),
    CreateResponse(CreateResponse),
    DeleteRequest(DeleteRequest),
    DeleteResponse(DeleteResponse),
}

pub struct CreateRequest {
    pub obj: ResourceObj,
}

pub struct CreateResponse {
    pub obj: ResourceObj,
}

pub struct DeleteRequest {
    pub key: ResourceKey,
}

pub struct DeleteResponse {
    pub key: ResourceKey,
}

pub struct CState {
    pub resources: Map<ResourceKey, ResourceObj>,
    pub messages: Set<Message>,
    // TODO: attached should be a field in Volume or Pod
    pub attached: Set<Seq<char>>,
}

/**
 *                  k8s_handle_request(cr)
 *                           |
 *              controller_send_create_sts
 *                           |
 *                   k8s_handle_request(sts)
 *                     /           \
 *                    /             \
 *                   |               |
 * k8s_handle_request(pod)           k8s_handle_request(vol)
 *                   |               |
 *                    \             /
 *                     \           /
 *                  k8s_attach_vol_to_pod
 *
 *
 * Note that in a real controller:
 * 1. Controllers usually issue sync call to k8s. It will only proceed after it
 * receives the response of the last call.
 * 2. Controllers' reconcile functions are usually single-threaded.
 * 3. Controllers don't and can't make decisions based on the sent messages.
 * Controllers rely on the response from the k8s and its local cache to make decision.
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

pub open spec fn resource_exists(s: CState, key: ResourceKey) -> bool {
    s.resources.dom().contains(key)
}

pub open spec fn create_req_msg(key: ResourceKey) -> Message {
    Message::CreateRequest(CreateRequest{
        obj: ResourceObj{
            key: key,
        },
    })
}

pub open spec fn create_resp_msg(key: ResourceKey) -> Message {
    Message::CreateResponse(CreateResponse{
        obj: ResourceObj{
            key: key,
        },
    })
}

pub open spec fn delete_req_msg(key: ResourceKey) -> Message {
    Message::DeleteRequest(DeleteRequest{
        key: key,
    })
}

pub open spec fn delete_resp_msg(key: ResourceKey) -> Message {
    Message::DeleteResponse(DeleteResponse{
        key: key,
    })
}

pub open spec fn init() -> StatePred<CState> {
    |s: CState| {
        &&& s.resources === Map::empty()
        &&& s.messages === Set::empty()
        &&& s.attached === Set::empty()
    }
}

pub open spec fn external_send_create_cr(res: ResourceObj) -> ActionPred<CState> {
    |s: CState, s_prime: CState| {
        &&& res.key.kind.is_CustomResourceKind()
        &&& s_prime === CState {
            messages: s.messages.insert(create_req_msg(res.key)),
            ..s
        }
    }
}

pub open spec fn external_send_delete_cr(res: ResourceObj) -> ActionPred<CState> {
    |s: CState, s_prime: CState| {
        &&& res.key.kind.is_CustomResourceKind()
        &&& s_prime === CState {
            messages: s.messages.insert(delete_req_msg(res.key)),
            ..s
        }
    }
}

pub open spec fn controller_send_create_sts_pre(msg: Message) -> StatePred<CState> {
    |s| {
        &&& message_sent(s, msg)
        &&& msg.is_CreateResponse()
        &&& msg.get_CreateResponse_0().obj.key.kind.is_CustomResourceKind()
    }
}

pub open spec fn controller_send_create_sts(msg: Message) -> ActionPred<CState> {
    |s, s_prime| {
        &&& controller_send_create_sts_pre(msg)(s)
        &&& s_prime === CState {
            messages: s.messages.insert(create_req_msg(ResourceKey{name: msg.get_CreateResponse_0().obj.key.name + sts_suffix(), kind: ResourceKind::StatefulSetKind})),
            ..s
        }
    }
}

pub open spec fn controller_send_delete_sts_pre(msg: Message) -> StatePred<CState> {
    |s| {
        &&& message_sent(s, msg)
        &&& msg.is_DeleteResponse()
        &&& msg.get_DeleteResponse_0().key.kind.is_CustomResourceKind()
    }
}

pub open spec fn controller_send_delete_sts(msg: Message) -> ActionPred<CState> {
    |s, s_prime| {
        &&& controller_send_delete_sts_pre(msg)(s)
        &&& s_prime === CState {
            messages: s.messages.insert(delete_req_msg(ResourceKey{name: msg.get_DeleteResponse_0().key.name + sts_suffix(), kind: ResourceKind::StatefulSetKind})),
            ..s
        }
    }
}

pub open spec fn k8s_handle_request_pre(msg: Message) -> StatePred<CState> {
    |s| {
        &&& message_sent(s, msg)
        &&& msg.is_CreateRequest() || msg.is_DeleteRequest()
    }
}

pub open spec fn update_resources_with(s: CState, msg: Message) -> Map<ResourceKey, ResourceObj>
    recommends
        msg.is_CreateRequest() || msg.is_DeleteRequest(),
{
    if msg.is_CreateRequest() {
        if s.resources.dom().contains(msg.get_CreateRequest_0().obj.key) {
            s.resources
        } else {
            s.resources.insert(msg.get_CreateRequest_0().obj.key, msg.get_CreateRequest_0().obj)
        }
    } else {
        if !s.resources.dom().contains(msg.get_DeleteRequest_0().key) {
            s.resources
        } else {
            s.resources.remove(msg.get_DeleteRequest_0().key)
        }
    }
}

pub open spec fn update_messages_with(s: CState, msg: Message) -> Set<Message>
    recommends
        msg.is_CreateRequest() || msg.is_DeleteRequest(),
{
    if msg.is_CreateRequest() {
        if msg.get_CreateRequest_0().obj.key.kind.is_StatefulSetKind() {
            s.messages.insert(create_resp_msg(msg.get_CreateRequest_0().obj.key))
                .insert(create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind}))
                .insert(create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind}))
        } else {
            s.messages.insert(create_resp_msg(msg.get_CreateRequest_0().obj.key))
        }
    } else {
        if msg.get_DeleteRequest_0().key.kind.is_StatefulSetKind() {
            s.messages.insert(delete_resp_msg(msg.get_DeleteRequest_0().key))
                .insert(delete_req_msg(ResourceKey{name: msg.get_DeleteRequest_0().key.name + pod_suffix(), kind: ResourceKind::PodKind}))
                .insert(delete_req_msg(ResourceKey{name: msg.get_DeleteRequest_0().key.name + vol_suffix(), kind: ResourceKind::VolumeKind}))
        } else {
            s.messages.insert(delete_resp_msg(msg.get_DeleteRequest_0().key))
        }
    }
}

pub open spec fn k8s_handle_request(msg: Message) -> ActionPred<CState> {
    |s, s_prime| {
        &&& k8s_handle_request_pre(msg)(s)
        &&& s_prime === CState {
            resources: update_resources_with(s, msg),
            messages: update_messages_with(s, msg),
            ..s
        }
    }
}

pub open spec fn k8s_attach_vol_to_pod_pre(sts_name: Seq<char>) -> StatePred<CState> {
    |s| {
        &&& resource_exists(s, ResourceKey{name: sts_name + pod_suffix(), kind: ResourceKind::PodKind})
        &&& resource_exists(s, ResourceKey{name: sts_name + vol_suffix(), kind: ResourceKind::VolumeKind})
    }
}

/// k8s_attach_vol_to_pod should be part of the k8s built-in statefulset controller's job
/// and the implementation here is not very realistic
/// What actually happened in statefulset controller is that:
/// it creates the volume, then creates the pod.
/// The volume is already attached to the pod when the pod gets created.
pub open spec fn k8s_attach_vol_to_pod(sts_name: Seq<char>) -> ActionPred<CState> {
    |s, s_prime| {
        &&& k8s_attach_vol_to_pod_pre(sts_name)(s)
        &&& s_prime === CState {
            attached: s.attached.insert(sts_name),
            ..s
        }
    }
}

pub open spec fn stutter() -> ActionPred<CState> {
    |s, s_prime| s === s_prime
}

pub enum ActionLabel {
    ExternalSendCreateCR(ResourceObj),
    ExternalSendDeleteCR(ResourceObj),
    ControllerSendCreateSts(Message),
    ControllerSendDeleteSts(Message),
    K8sHandleRequest(Message),
    K8sAttachVolToPod(Seq<char>),
    Stutter
}

pub open spec fn next_step(s: CState, s_prime: CState, action_label: ActionLabel) -> bool {
    match action_label {
        ActionLabel::ExternalSendCreateCR(res) => external_send_create_cr(res)(s, s_prime),
        ActionLabel::ExternalSendDeleteCR(res) => external_send_delete_cr(res)(s, s_prime),
        ActionLabel::ControllerSendCreateSts(msg) => controller_send_create_sts(msg)(s, s_prime),
        ActionLabel::ControllerSendDeleteSts(msg) => controller_send_delete_sts(msg)(s, s_prime),
        ActionLabel::K8sHandleRequest(msg) => k8s_handle_request(msg)(s, s_prime),
        ActionLabel::K8sAttachVolToPod(cr_name) => k8s_attach_vol_to_pod(cr_name)(s, s_prime),
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
    .and(tla_forall(|msg| weak_fairness(controller_send_delete_sts(msg))))
    .and(tla_forall(|msg| weak_fairness(k8s_handle_request(msg))))
    .and(tla_forall(|cr_name| weak_fairness(k8s_attach_vol_to_pod(cr_name))))
}

pub proof fn controller_send_create_sts_enabled(msg: Message)
    ensures
        forall |s| #[trigger] controller_send_create_sts_pre(msg)(s)
            ==> enabled(controller_send_create_sts(msg))(s),
{
    assert forall |s| #[trigger] controller_send_create_sts_pre(msg)(s)
    implies enabled(controller_send_create_sts(msg))(s) by {
        let witness_s_prime = CState {
            messages: s.messages.insert(create_req_msg(ResourceKey{name: msg.get_CreateResponse_0().obj.key.name + sts_suffix(), kind: ResourceKind::StatefulSetKind})),
            ..s
        };
        assert(controller_send_create_sts(msg)(s, witness_s_prime));
    };
}

pub proof fn controller_send_delete_sts_enabled(msg: Message)
    ensures
        forall |s| #[trigger] controller_send_delete_sts_pre(msg)(s)
            ==> enabled(controller_send_delete_sts(msg))(s),
{
    assert forall |s| #[trigger] controller_send_delete_sts_pre(msg)(s)
    implies enabled(controller_send_delete_sts(msg))(s) by {
        let witness_s_prime = CState {
            messages: s.messages.insert(delete_req_msg(ResourceKey{name: msg.get_DeleteResponse_0().key.name + sts_suffix(), kind: ResourceKind::StatefulSetKind})),
            ..s
        };
        assert(controller_send_delete_sts(msg)(s, witness_s_prime));
    };
}

pub proof fn k8s_handle_request_enabled(msg: Message)
    ensures
        forall |s| #[trigger] k8s_handle_request_pre(msg)(s)
            ==> enabled(k8s_handle_request(msg))(s),
{
    assert forall |s| #[trigger] k8s_handle_request_pre(msg)(s)
    implies enabled(k8s_handle_request(msg))(s) by {
        let witness_s_prime = CState {
            resources: update_resources_with(s, msg),
            messages: update_messages_with(s, msg),
            ..s
        };
        assert(k8s_handle_request(msg)(s, witness_s_prime));
    };
}

pub proof fn k8s_attach_vol_to_pod_enabled(cr_name: Seq<char>)
    ensures
        forall |s| #[trigger] k8s_attach_vol_to_pod_pre(cr_name)(s)
            ==> enabled(k8s_attach_vol_to_pod(cr_name))(s),
{
    assert forall |s| #[trigger] k8s_attach_vol_to_pod_pre(cr_name)(s)
    implies enabled(k8s_attach_vol_to_pod(cr_name))(s) by {
        let witness_s_prime = CState {
            attached: s.attached.insert(cr_name),
            ..s
        };
        assert(k8s_attach_vol_to_pod(cr_name)(s, witness_s_prime));
    };
}

}
