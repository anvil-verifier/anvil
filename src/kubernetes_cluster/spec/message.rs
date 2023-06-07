// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, dynamic::*, error::*};
use crate::pervasive_ext::string_view::*;
use builtin::*;
use builtin_macros::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct MessageOps {
    pub recv: Option<Message>,
    pub send: Multiset<Message>,
}

pub struct Message {
    pub src: HostId,
    pub dst: HostId,
    pub content: MessageContent,
}

#[is_variant]
pub enum HostId {
    KubernetesAPI,
    CustomController,
    Client,
}

pub type RestId = nat;

// RestIdAllocator allocates unique RestId for each request sent by the controller.
// The Kubernetes API state machine ensures the response will carry the same RestId.
pub struct RestIdAllocator {
    pub rest_id_counter: RestId,
}

impl RestIdAllocator {
    // Allocate a RestId which is the current rest_id_counter
    // and also returns a new RestIdAllocator with a different rest_id_counter.
    //
    // An important assumption of RestIdAllocator is that the user (i.e., state machine)
    // after allocating one RestId, will use the returned new RestIdAllocator
    // to allocate the next RestId.
    // With this assumption, the user of RestIdAllocator always gets a RestId
    // which differs from all the RestIds allocated before because the
    // returned RestIdAllocator has a incremented rest_id_counter.
    //
    // Besides the uniqueness, the allocated RestId can also serve as a timestamp
    // if we need to say some Rest messages are sent before the others.
    pub open spec fn allocate(self) -> (Self, RestId) {
        (RestIdAllocator {
            rest_id_counter: self.rest_id_counter + 1,
        }, self.rest_id_counter)
    }
}

// Each MessageContent is a request/response and a rest id
#[is_variant]
pub enum MessageContent {
    APIRequest(APIRequest, RestId),
    APIResponse(APIResponse, RestId),
}

// WatchEvent is actually also a type of message
// but since we don't reason about the message flows inside k8s API for now
// so we don't include it into MessageContent
#[is_variant]
pub enum WatchEvent {
    AddedEvent(AddedEvent),
    ModifiedEvent(ModifiedEvent),
    DeletedEvent(DeletedEvent),
}

pub struct AddedEvent {
    pub obj: DynamicObjectView,
}

pub struct ModifiedEvent {
    pub obj: DynamicObjectView,
}

pub struct DeletedEvent {
    pub obj: DynamicObjectView,
}

// Some handy methods for pattern matching and retrieving information from MessageContent
impl MessageContent {
    pub open spec fn is_get_request(self) -> bool {
        &&& self.is_APIRequest()
        &&& self.get_APIRequest_0().is_GetRequest()
    }

    pub open spec fn get_get_request(self) -> GetRequest
        recommends
            self.is_get_request()
    {
        self.get_APIRequest_0().get_GetRequest_0()
    }

    pub open spec fn is_list_request(self) -> bool {
        &&& self.is_APIRequest()
        &&& self.get_APIRequest_0().is_ListRequest()
    }

    pub open spec fn get_list_request(self) -> ListRequest
        recommends
            self.is_list_request()
    {
        self.get_APIRequest_0().get_ListRequest_0()
    }

    pub open spec fn is_create_request(self) -> bool {
        &&& self.is_APIRequest()
        &&& self.get_APIRequest_0().is_CreateRequest()
    }

    pub open spec fn get_create_request(self) -> CreateRequest
        recommends
            self.is_create_request()
    {
        self.get_APIRequest_0().get_CreateRequest_0()
    }

    pub open spec fn is_delete_request(self) -> bool {
        &&& self.is_APIRequest()
        &&& self.get_APIRequest_0().is_DeleteRequest()
    }

    pub open spec fn get_delete_request(self) -> DeleteRequest
        recommends
            self.is_delete_request()
    {
        self.get_APIRequest_0().get_DeleteRequest_0()
    }

    pub open spec fn is_update_request(self) -> bool {
        &&& self.is_APIRequest()
        &&& self.get_APIRequest_0().is_UpdateRequest()
    }

    pub open spec fn get_update_request(self) -> UpdateRequest
        recommends
            self.is_update_request()
    {
        self.get_APIRequest_0().get_UpdateRequest_0()
    }

    pub open spec fn get_req_id(self) -> RestId
        recommends
            self.is_APIRequest()
    {
        self.get_APIRequest_1()
    }

    pub open spec fn is_get_response(self) -> bool {
        &&& self.is_APIResponse()
        &&& self.get_APIResponse_0().is_GetResponse()
    }

    pub open spec fn get_get_response(self) -> GetResponse
        recommends
            self.is_get_response()
    {
        self.get_APIResponse_0().get_GetResponse_0()
    }

    pub open spec fn is_create_response(self) -> bool {
        &&& self.is_APIResponse()
        &&& self.get_APIResponse_0().is_CreateResponse()
    }

    pub open spec fn get_create_response(self) -> CreateResponse
        recommends
            self.is_create_response()
    {
        self.get_APIResponse_0().get_CreateResponse_0()
    }

    pub open spec fn is_delete_response(self) -> bool {
        &&& self.is_APIResponse()
        &&& self.get_APIResponse_0().is_DeleteResponse()
    }

    pub open spec fn get_delete_response(self) -> DeleteResponse
        recommends
            self.is_delete_response()
    {
        self.get_APIResponse_0().get_DeleteResponse_0()
    }

    pub open spec fn is_list_response(self) -> bool {
        &&& self.is_APIResponse()
        &&& self.get_APIResponse_0().is_ListResponse()
    }

    pub open spec fn get_list_response(self) -> ListResponse
        recommends
            self.is_list_response()
    {
        self.get_APIResponse_0().get_ListResponse_0()
    }

    pub open spec fn get_resp_id(self) -> RestId
        recommends
            self.is_APIResponse()
    {
        self.get_APIResponse_1()
    }

    pub open spec fn get_rest_id(self) -> RestId
    {
        match self {
            MessageContent::APIRequest(_, _) => self.get_APIRequest_1(),
            MessageContent::APIResponse(_, _) => self.get_APIResponse_1()
        }
    }
}

pub open spec fn is_ok_resp(resp: APIResponse) -> bool {
    match resp {
        APIResponse::GetResponse(get_resp) => get_resp.res.is_Ok(),
        APIResponse::ListResponse(list_resp) => list_resp.res.is_Ok(),
        APIResponse::CreateResponse(create_resp) => create_resp.res.is_Ok(),
        APIResponse::DeleteResponse(delete_resp) => delete_resp.res.is_Ok(),
        APIResponse::UpdateResponse(update_resp) => update_resp.res.is_Ok(),
    }
}

// TODO: maybe the predicate should not check if resp_msg is a response message
pub open spec fn resp_msg_matches_req_msg(resp_msg: Message, req_msg: Message) -> bool {
    &&& resp_msg.content.is_APIResponse()
    &&& req_msg.content.is_APIRequest()
    &&& resp_msg.dst == req_msg.src
    &&& resp_msg.src == req_msg.dst
    &&& resp_msg.content.get_APIResponse_1() == req_msg.content.get_APIRequest_1()
    &&& match resp_msg.content.get_APIResponse_0() {
        APIResponse::GetResponse(_) => req_msg.content.get_APIRequest_0().is_GetRequest(),
        APIResponse::ListResponse(_) => req_msg.content.get_APIRequest_0().is_ListRequest(),
        APIResponse::CreateResponse(_) => req_msg.content.get_APIRequest_0().is_CreateRequest(),
        APIResponse::DeleteResponse(_) => req_msg.content.get_APIRequest_0().is_DeleteRequest(),
        APIResponse::UpdateResponse(_) => req_msg.content.get_APIRequest_0().is_UpdateRequest(),
    }
}

pub open spec fn form_msg(src: HostId, dst: HostId, msg_content: MessageContent) -> Message {
    Message{
        src: src,
        dst: dst,
        content: msg_content,
    }
}

pub open spec fn form_get_resp_msg(req_msg: Message, result: Result<DynamicObjectView, APIError>) -> Message
    recommends req_msg.content.is_get_request(),
{
    form_msg(req_msg.dst, req_msg.src, get_resp_msg_content(result, req_msg.content.get_req_id()))
}

pub open spec fn form_list_resp_msg(req_msg: Message, result: Result<Seq<DynamicObjectView>, APIError>) -> Message
    recommends req_msg.content.is_list_request(),
{
    form_msg(req_msg.dst, req_msg.src, list_resp_msg_content(result, req_msg.content.get_req_id()))
}

pub open spec fn form_create_resp_msg(req_msg: Message, result: Result<DynamicObjectView, APIError>) -> Message
    recommends req_msg.content.is_create_request(),
{
    form_msg(req_msg.dst, req_msg.src, create_resp_msg_content(result, req_msg.content.get_req_id()))
}

pub open spec fn form_delete_resp_msg(req_msg: Message, result: Result<DynamicObjectView, APIError>) -> Message
    recommends req_msg.content.is_delete_request(),
{
    form_msg(req_msg.dst, req_msg.src, delete_resp_msg_content(result, req_msg.content.get_req_id()))
}

pub open spec fn form_update_resp_msg(req_msg: Message, result: Result<DynamicObjectView, APIError>) -> Message
    recommends req_msg.content.is_update_request(),
{
    form_msg(req_msg.dst, req_msg.src, update_resp_msg_content(result, req_msg.content.get_req_id()))
}

pub open spec fn added_event(obj: DynamicObjectView) -> WatchEvent {
    WatchEvent::AddedEvent(AddedEvent{
        obj: obj
    })
}

pub open spec fn modified_event(obj: DynamicObjectView) -> WatchEvent {
    WatchEvent::ModifiedEvent(ModifiedEvent{
        obj: obj
    })
}

pub open spec fn deleted_event(obj: DynamicObjectView) -> WatchEvent {
    WatchEvent::DeletedEvent(DeletedEvent{
        obj: obj
    })
}

pub open spec fn get_req_msg_content(key: ObjectRef, req_id: RestId) -> MessageContent {
    MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{
        key: key,
    }), req_id)
}

pub open spec fn list_req_msg_content(kind: Kind, namespace: StringView, req_id: RestId) -> MessageContent {
    MessageContent::APIRequest(APIRequest::ListRequest(ListRequest{
        kind: kind,
        namespace: namespace,
    }), req_id)
}

pub open spec fn create_req_msg_content(namespace: StringView, obj: DynamicObjectView, req_id: RestId) -> MessageContent {
    MessageContent::APIRequest(APIRequest::CreateRequest(CreateRequest{
        namespace: namespace,
        obj: obj,
    }), req_id)
}

pub open spec fn delete_req_msg_content(key: ObjectRef, req_id: RestId) -> MessageContent {
    MessageContent::APIRequest(APIRequest::DeleteRequest(DeleteRequest{
        key: key,
    }), req_id)
}

pub open spec fn update_req_msg_content(key: ObjectRef, obj: DynamicObjectView, req_id: RestId) -> MessageContent {
    MessageContent::APIRequest(APIRequest::UpdateRequest(UpdateRequest{
        key: key,
        obj: obj,
    }), req_id)
}

pub open spec fn get_resp_msg_content(res: Result<DynamicObjectView, APIError>, resp_id: RestId) -> MessageContent {
    MessageContent::APIResponse(APIResponse::GetResponse(GetResponse{
        res: res,
    }), resp_id)
}

pub open spec fn list_resp_msg_content(res: Result<Seq<DynamicObjectView>, APIError>, resp_id: RestId) -> MessageContent {
    MessageContent::APIResponse(APIResponse::ListResponse(ListResponse{
        res: res,
    }), resp_id)
}

pub open spec fn create_resp_msg_content(res: Result<DynamicObjectView, APIError>, resp_id: RestId) -> MessageContent {
    MessageContent::APIResponse(APIResponse::CreateResponse(CreateResponse{
        res: res,
    }), resp_id)
}

pub open spec fn delete_resp_msg_content(res: Result<DynamicObjectView, APIError>, resp_id: RestId) -> MessageContent {
    MessageContent::APIResponse(APIResponse::DeleteResponse(DeleteResponse{
        res: res,
    }), resp_id)
}

pub open spec fn update_resp_msg_content(res: Result<DynamicObjectView, APIError>, resp_id: RestId) -> MessageContent {
    MessageContent::APIResponse(APIResponse::UpdateResponse(UpdateResponse{
        res: res,
    }), resp_id)
}

}
