// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::kubernetes_cluster::spec::{common::*, kubernetes_api::common::*};
use crate::pervasive::{map::*, option::*, result::*, seq::*, set::*};
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn transition_by_statefulset_controller(msg: Message, s: KubernetesAPIState) -> Set<Message>
    recommends
        msg.content.is_WatchEvent(),
{
    let src = HostId::KubernetesAPI;
    // Here dst is also KubernetesAPI because etcd, apiserver and built-in controllers are all in the same state machine.
    // In reality, the message is sent from the built-in controller to apiserver then to etcd.
    let dst = HostId::KubernetesAPI;
    if msg.is_watch_event_of_kind(ResourceKind::StatefulSetKind) {
        if msg.is_added_event() {
            let obj = msg.get_added_event().obj;
            set![
                form_msg(src, dst, create_req_msg(ResourceObj{key: ResourceKey{name: obj.key.name + pod_suffix(), namespace: obj.key.namespace, kind: ResourceKind::PodKind}})),
                form_msg(src, dst, create_req_msg(ResourceObj{key: ResourceKey{name: obj.key.name + vol_suffix(), namespace: obj.key.namespace, kind: ResourceKind::VolumeKind}}))
            ]
        } else if msg.is_modified_event() {
            set![]
        } else {
            let obj = msg.get_deleted_event().obj;
            set![
                    form_msg(src, dst, delete_req_msg(ResourceKey{name: obj.key.name + pod_suffix(), namespace: obj.key.namespace, kind: ResourceKind::PodKind})),
                    form_msg(src, dst, delete_req_msg(ResourceKey{name: obj.key.name + vol_suffix(), namespace: obj.key.namespace, kind: ResourceKind::VolumeKind}))
                ]
        }
    } else {
        set![]
    }
}

}
