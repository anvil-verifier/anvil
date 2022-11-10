// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::{option::*, seq::*, set::*, string::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

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

pub struct ResourceObj {
    pub key: ResourceKey,
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

#[is_variant]
pub enum Message {
    CreateRequest(CreateRequest),
    CreateResponse(CreateResponse),
    DeleteRequest(DeleteRequest),
    DeleteResponse(DeleteResponse),
}

pub struct MessageOps {
    pub recv: Option<Message>,
    pub send: Set<Message>,
}

pub open spec fn sts_suffix() -> Seq<char> {
    new_strlit("_sts")@
}

pub open spec fn pod_suffix() -> Seq<char> {
    new_strlit("_pod")@
}

pub open spec fn vol_suffix() -> Seq<char> {
    new_strlit("_vol")@
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

}
