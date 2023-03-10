// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{common::*, kubernetes_api::common::*};
use crate::pervasive::{map::*, multiset::*, option::*, result::*, seq::*};
use builtin::*;
use builtin_macros::*;

verus! {

// TODO: complete the statefulset controller spec
pub open spec fn transition_by_statefulset_controller(msg: Message, s: KubernetesAPIState) -> Multiset<Message>
    recommends
        msg.content.is_WatchEvent(),
{
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
    Multiset::empty()
}

}
