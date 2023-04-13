// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{channel::*, kubernetes_api::common::*, message::*};
use vstd::{map::*, multiset::*, option::*, result::*, seq::*};
use builtin::*;
use builtin_macros::*;

verus! {

// TODO: complete the statefulset controller spec
pub open spec fn transition_by_statefulset_controller(event: WatchEvent, s: KubernetesAPIState, chan_manager: ChannelManager) -> (ChannelManager, Multiset<Message>) {
    let src = HostId::KubernetesAPI;
    // Here dst is also KubernetesAPI because etcd, apiserver and built-in controllers are all in the same state machine.
    // In reality, the message is sent from the built-in controller to apiserver then to etcd.

    let dst = HostId::KubernetesAPI;
    // if msg.content.is_watch_event_of_kind(Kind::StatefulSetKind) {
    //     if msg.content.is_added_event() {
    //         let obj = msg.content.get_added_event().obj;
    //         Multiset::empty()
    //             .insert(form_msg(src, dst, create_req_msg_content(KubernetesObject{key: ObjectRef{name: obj.key.name + pod_suffix(), namespace: obj.key.namespace, kind: Kind::PodKind}}, s.req_id)))
    //             .insert(form_msg(src, dst, create_req_msg_content(KubernetesObject{key: ObjectRef{name: obj.key.name + vol_suffix(), namespace: obj.key.namespace, kind: Kind::VolumeKind}}, s.req_id + 1)))
    //     } else if msg.content.is_modified_event() {
    //         Multiset::empty()
    //     } else {
    //         let obj = msg.content.get_deleted_event().obj;
    //         Multiset::empty()
    //             .insert(form_msg(src, dst, delete_req_msg_content(ObjectRef{name: obj.key.name + pod_suffix(), namespace: obj.key.namespace, kind: Kind::PodKind}, s.req_id)))
    //             .insert(form_msg(src, dst, delete_req_msg_content(ObjectRef{name: obj.key.name + vol_suffix(), namespace: obj.key.namespace, kind: Kind::VolumeKind}, s.req_id + 1)))
    //     }
    // } else {
    //     Multiset::empty()
    // }
    (chan_manager, Multiset::empty())
}

}
