// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::function::*;
use crate::pervasive::{multiset::*, option::*, result::*, seq::*, set::*, string::*};
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

#[is_variant]
pub enum ResourceKind {
    CustomResourceKind,
    ConfigMapKind,
    StatefulSetKind,
    PodKind,
    VolumeKind,
}

pub struct ResourceKey {
    pub name: Seq<char>,
    pub namespace: Seq<char>,
    pub kind: ResourceKind,
}

pub struct ResourceObj {
    pub key: ResourceKey,
}

#[is_variant]
pub enum APIError {
    ObjectNotFound,
    ObjectAlreadyExists,
}

pub struct GetRequest {
    pub key: ResourceKey,
}

pub struct ListRequest {
    pub kind: ResourceKind,
}

pub struct CreateRequest {
    pub obj: ResourceObj,
}

pub struct DeleteRequest {
    pub key: ResourceKey,
}

#[is_variant]
pub enum APIRequest {
    GetRequest(GetRequest),
    ListRequest(ListRequest),
    CreateRequest(CreateRequest),
    DeleteRequest(DeleteRequest),
}

pub struct GetResponse {
    pub res: Result<ResourceObj, APIError>,
    pub req: GetRequest,
}

pub struct ListResponse {
    pub res: Result<Seq<ResourceObj>, APIError>,
    pub req: ListRequest,
}

pub struct CreateResponse {
    pub res: Result<ResourceObj, APIError>,
    pub req: CreateRequest,
}

pub struct DeleteResponse {
    pub res: Result<ResourceObj, APIError>,
    pub req: DeleteRequest,
}

#[is_variant]
pub enum APIResponse {
    GetResponse(GetResponse),
    ListResponse(ListResponse),
    CreateResponse(CreateResponse),
    DeleteResponse(DeleteResponse),
}

pub struct AddedEvent {
    pub obj: ResourceObj,
}

pub struct ModifiedEvent {
    pub obj: ResourceObj,
}

pub struct DeletedEvent {
    pub obj: ResourceObj,
}

#[is_variant]
pub enum WatchEvent {
    AddedEvent(AddedEvent),
    ModifiedEvent(ModifiedEvent),
    DeletedEvent(DeletedEvent),
}

#[is_variant]
pub enum MessageContent {
    APIRequest(APIRequest, nat),
    APIResponse(APIResponse, nat),
    WatchEvent(WatchEvent),
}

#[is_variant]
pub enum HostId {
    KubernetesAPI,
    CustomController,
    Client,
}

pub struct Message {
    pub src: HostId,
    pub dst: HostId,
    pub content: MessageContent,
}

impl Message {
    pub open spec fn is_read_request(self) -> bool {
        &&& self.content.is_APIRequest()
        &&& (self.content.get_APIRequest_0().is_GetRequest() || self.content.get_APIRequest_0().is_ListRequest())
    }

    pub open spec fn is_write_request(self) -> bool {
        &&& self.content.is_APIRequest()
        &&& (self.content.get_APIRequest_0().is_CreateRequest() || self.content.get_APIRequest_0().is_DeleteRequest())
    }

    pub open spec fn is_write_request_of_kind(self, kind: ResourceKind) -> bool {
        &&& self.is_write_request()
        &&& match self.content.get_APIRequest_0() {
            APIRequest::CreateRequest(req) => req.obj.key.kind === kind,
            APIRequest::DeleteRequest(req) => req.key.kind === kind,
            _ => false,
        }
    }

    pub open spec fn is_get_request(self) -> bool {
        &&& self.content.is_APIRequest()
        &&& self.content.get_APIRequest_0().is_GetRequest()
    }

    pub open spec fn get_get_request(self) -> GetRequest
        recommends
            self.is_get_request()
    {
        self.content.get_APIRequest_0().get_GetRequest_0()
    }

    pub open spec fn is_list_request(self) -> bool {
        &&& self.content.is_APIRequest()
        &&& self.content.get_APIRequest_0().is_ListRequest()
    }

    pub open spec fn get_list_request(self) -> ListRequest
        recommends
            self.is_list_request()
    {
        self.content.get_APIRequest_0().get_ListRequest_0()
    }

    pub open spec fn is_create_request(self) -> bool {
        &&& self.content.is_APIRequest()
        &&& self.content.get_APIRequest_0().is_CreateRequest()
    }

    pub open spec fn get_create_request(self) -> CreateRequest
        recommends
            self.is_create_request()
    {
        self.content.get_APIRequest_0().get_CreateRequest_0()
    }

    pub open spec fn is_delete_request(self) -> bool {
        &&& self.content.is_APIRequest()
        &&& self.content.get_APIRequest_0().is_DeleteRequest()
    }

    pub open spec fn get_delete_request(self) -> DeleteRequest
        recommends
            self.is_delete_request()
    {
        self.content.get_APIRequest_0().get_DeleteRequest_0()
    }

    pub open spec fn get_req_id(self) -> nat
        recommends
            self.content.is_APIRequest()
    {
        self.content.get_APIRequest_1()
    }

    pub open spec fn is_get_response(self) -> bool {
        &&& self.content.is_APIResponse()
        &&& self.content.get_APIResponse_0().is_GetResponse()
    }

    pub open spec fn get_get_response(self) -> GetResponse
        recommends
            self.is_get_response()
    {
        self.content.get_APIResponse_0().get_GetResponse_0()
    }

    pub open spec fn is_create_response(self) -> bool {
        &&& self.content.is_APIResponse()
        &&& self.content.get_APIResponse_0().is_CreateResponse()
    }

    pub open spec fn get_create_response(self) -> CreateResponse
        recommends
            self.is_create_response()
    {
        self.content.get_APIResponse_0().get_CreateResponse_0()
    }

    pub open spec fn is_delete_response(self) -> bool {
        &&& self.content.is_APIResponse()
        &&& self.content.get_APIResponse_0().is_DeleteResponse()
    }

    pub open spec fn get_delete_response(self) -> DeleteResponse
        recommends
            self.is_delete_response()
    {
        self.content.get_APIResponse_0().get_DeleteResponse_0()
    }

    pub open spec fn get_resp_id(self) -> nat
        recommends
            self.content.is_APIResponse()
    {
        self.content.get_APIResponse_1()
    }

    pub open spec fn is_watch_event_of_kind(self, kind: ResourceKind) -> bool {
        &&& self.content.is_WatchEvent()
        &&& match self.content.get_WatchEvent_0() {
            WatchEvent::AddedEvent(added) => added.obj.key.kind === kind,
            WatchEvent::ModifiedEvent(modified) => modified.obj.key.kind === kind,
            WatchEvent::DeletedEvent(deleted) => deleted.obj.key.kind === kind,
        }
    }

    pub open spec fn is_added_event(self) -> bool {
        &&& self.content.is_WatchEvent()
        &&& self.content.get_WatchEvent_0().is_AddedEvent()
    }

    pub open spec fn get_added_event(self) -> AddedEvent
        recommends
            self.is_added_event()
    {
        self.content.get_WatchEvent_0().get_AddedEvent_0()
    }

    pub open spec fn is_modified_event(self) -> bool {
        &&& self.content.is_WatchEvent()
        &&& self.content.get_WatchEvent_0().is_ModifiedEvent()
    }

    pub open spec fn get_modified_event(self) -> ModifiedEvent
        recommends
            self.is_modified_event()
    {
        self.content.get_WatchEvent_0().get_ModifiedEvent_0()
    }

    pub open spec fn is_deleted_event(self) -> bool {
        &&& self.content.is_WatchEvent()
        &&& self.content.get_WatchEvent_0().is_DeletedEvent()
    }

    pub open spec fn get_deleted_event(self) -> DeletedEvent
        recommends
            self.is_deleted_event()
    {
        self.content.get_WatchEvent_0().get_DeletedEvent_0()
    }
}

pub open spec fn is_ok_resp(resp: APIResponse) -> bool {
    match resp {
        APIResponse::GetResponse(get_resp) => get_resp.res.is_Ok(),
        APIResponse::ListResponse(list_resp) => list_resp.res.is_Ok(),
        APIResponse::CreateResponse(create_resp) => create_resp.res.is_Ok(),
        APIResponse::DeleteResponse(delete_resp) => delete_resp.res.is_Ok(),
    }
}

pub open spec fn resp_matches_req(resp: APIResponse, req: APIRequest) -> bool {
    match resp {
        APIResponse::GetResponse(get_resp) => {
            &&& req.is_GetRequest()
            &&& get_resp.req === req.get_GetRequest_0()
        },
        APIResponse::ListResponse(list_resp) => {
            &&& req.is_ListRequest()
            &&& list_resp.req === req.get_ListRequest_0()
        },
        APIResponse::CreateResponse(create_resp) => {
            &&& req.is_CreateRequest()
            &&& create_resp.req === req.get_CreateRequest_0()
        },
        APIResponse::DeleteResponse(delete_resp) => {
            &&& req.is_DeleteRequest()
            &&& delete_resp.req === req.get_DeleteRequest_0()
        },
    }
}

// TODO: maybe the predicate should not check if resp_msg is a response message
pub open spec fn resp_msg_matches_req_msg(resp_msg: Message, req_msg: Message) -> bool {
    &&& resp_msg.content.is_APIResponse()
    &&& req_msg.content.is_APIRequest()
    &&& resp_msg.dst === req_msg.src
    &&& resp_msg.src === req_msg.dst
    &&& resp_matches_req(resp_msg.content.get_APIResponse_0(), req_msg.content.get_APIRequest_0())
    &&& resp_msg.content.get_APIResponse_1() === req_msg.content.get_APIRequest_1()
}

pub open spec fn cm_suffix() -> Seq<char> {
    new_strlit("_cm")@
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

pub open spec fn default_ns() -> Seq<char> {
    new_strlit("default")@
}

pub open spec fn form_msg(src: HostId, dst: HostId, msg_content: MessageContent) -> Message {
    Message{
        src: src,
        dst: dst,
        content: msg_content,
    }
}

pub open spec fn form_get_resp_msg(req_msg: Message, result: Result<ResourceObj, APIError>, resp_id: nat) -> Message
    recommends req_msg.is_get_request(),
{
    form_msg(req_msg.dst, req_msg.src, get_resp_msg(result, req_msg.get_get_request(), resp_id))
}

pub open spec fn added_event_msg(obj: ResourceObj) -> MessageContent {
    MessageContent::WatchEvent(WatchEvent::AddedEvent(AddedEvent{
        obj: obj
    }))
}

pub open spec fn modified_event_msg(obj: ResourceObj) -> MessageContent {
    MessageContent::WatchEvent(WatchEvent::ModifiedEvent(ModifiedEvent{
        obj: obj
    }))
}

pub open spec fn deleted_event_msg(obj: ResourceObj) -> MessageContent {
    MessageContent::WatchEvent(WatchEvent::DeletedEvent(DeletedEvent{
        obj: obj
    }))
}

pub open spec fn get_req_msg(key: ResourceKey, req_id: nat) -> MessageContent {
    MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{
        key: key,
    }), req_id)
}

pub open spec fn list_req_msg(kind: ResourceKind, req_id: nat) -> MessageContent {
    MessageContent::APIRequest(APIRequest::ListRequest(ListRequest{
        kind: kind,
    }), req_id)
}

pub open spec fn create_req(obj: ResourceObj) -> APIRequest {
    APIRequest::CreateRequest(CreateRequest{
        obj: obj,
    })
}

pub open spec fn create_req_msg(obj: ResourceObj, req_id: nat) -> MessageContent {
    MessageContent::APIRequest(create_req(obj), req_id)
}

pub open spec fn delete_req(key: ResourceKey) -> APIRequest {
    APIRequest::DeleteRequest(DeleteRequest{
        key: key,
    })
}

pub open spec fn delete_req_msg(key: ResourceKey, req_id: nat) -> MessageContent {
    MessageContent::APIRequest(delete_req(key), req_id)
}

pub open spec fn get_resp_msg(res: Result<ResourceObj, APIError>, req: GetRequest, resp_id: nat) -> MessageContent {
    MessageContent::APIResponse(APIResponse::GetResponse(GetResponse{
        res: res,
        req: req,
    }), resp_id)
}

pub open spec fn list_resp_msg(res: Result<Seq<ResourceObj>, APIError>, req: ListRequest, resp_id: nat) -> MessageContent {
    MessageContent::APIResponse(APIResponse::ListResponse(ListResponse{
        res: res,
        req: req,
    }), resp_id)
}

pub open spec fn create_resp_msg(res: Result<ResourceObj, APIError>, req: CreateRequest, resp_id: nat) -> MessageContent {
    MessageContent::APIResponse(APIResponse::CreateResponse(CreateResponse{
        res: res,
        req: req,
    }), resp_id)
}

pub open spec fn delete_resp_msg(res: Result<ResourceObj, APIError>, req: DeleteRequest, resp_id: nat) -> MessageContent {
    MessageContent::APIResponse(APIResponse::DeleteResponse(DeleteResponse{
        res: res,
        req: req,
    }), resp_id)
}

pub open spec fn msg_pred_call(msg_pred: FnSpec(Message) -> bool, m: Message) -> bool {
    msg_pred(m)
}

}
