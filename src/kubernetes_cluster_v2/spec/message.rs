// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, dynamic::*};
use crate::kubernetes_cluster_v2::spec::opaque::*;
use crate::vstd_ext::string_view::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub type RestId = nat;

pub type ExternalMessageContent = Opaque;

pub struct MessageOps {
    pub recv: Option<Message>,
    pub send: Multiset<Message>,
}

pub struct Message {
    pub src: HostId,
    pub dst: HostId,
    pub rest_id: RestId,
    pub content: MessageContent,
}

#[is_variant]
pub enum HostId {
    ApiServer,
    BuiltinController,
    Controller(int),
    External(int),
}

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
    APIRequest(APIRequest),
    APIResponse(APIResponse),
    ExternalRequest(ExternalMessageContent),
    ExternalResponse(ExternalMessageContent),
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

    pub open spec fn is_delete_request_with_key(self, key: ObjectRef) -> bool {
        &&& self.is_APIRequest()
        &&& self.get_APIRequest_0().is_DeleteRequest()
        &&& self.get_APIRequest_0().get_DeleteRequest_0().key == key
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

    pub open spec fn is_update_request_with_key(self, key: ObjectRef) -> bool {
        &&& self.is_APIRequest()
        &&& self.get_APIRequest_0().is_UpdateRequest()
        &&& self.get_APIRequest_0().get_UpdateRequest_0().key() == key
    }

    pub open spec fn get_update_request(self) -> UpdateRequest
        recommends
            self.is_update_request()
    {
        self.get_APIRequest_0().get_UpdateRequest_0()
    }

    pub open spec fn is_update_status_request(self) -> bool {
        &&& self.is_APIRequest()
        &&& self.get_APIRequest_0().is_UpdateStatusRequest()
    }

    pub open spec fn is_update_status_request_with_key(self, key: ObjectRef) -> bool {
        &&& self.is_APIRequest()
        &&& self.get_APIRequest_0().is_UpdateStatusRequest()
        &&& self.get_APIRequest_0().get_UpdateStatusRequest_0().key() == key
    }

    pub open spec fn get_update_status_request(self) -> UpdateStatusRequest
        recommends
            self.is_update_status_request()
    {
        self.get_APIRequest_0().get_UpdateStatusRequest_0()
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

    pub open spec fn is_update_response(self) -> bool {
        &&& self.is_APIResponse()
        &&& self.get_APIResponse_0().is_UpdateResponse()
    }

    pub open spec fn get_update_response(self) -> UpdateResponse
        recommends
            self.is_update_response()
    {
        self.get_APIResponse_0().get_UpdateResponse_0()
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
}

pub open spec fn is_ok_resp(resp: APIResponse) -> bool {
    match resp {
        APIResponse::GetResponse(get_resp) => get_resp.res.is_Ok(),
        APIResponse::ListResponse(list_resp) => list_resp.res.is_Ok(),
        APIResponse::CreateResponse(create_resp) => create_resp.res.is_Ok(),
        APIResponse::DeleteResponse(delete_resp) => delete_resp.res.is_Ok(),
        APIResponse::UpdateResponse(update_resp) => update_resp.res.is_Ok(),
        APIResponse::UpdateStatusResponse(update_status_resp) => update_status_resp.res.is_Ok(),
    }
}

impl Message {

pub open spec fn controller_req_msg(controller_id: int, req_id: RestId, req: APIRequest) -> Message {
    Message::form_msg(HostId::Controller(controller_id), HostId::ApiServer, req_id, MessageContent::APIRequest(req))
}

pub open spec fn controller_external_req_msg(controller_id: int, req_id: RestId, req: ExternalMessageContent) -> Message {
    Message::form_msg(HostId::Controller(controller_id), HostId::External(controller_id), req_id, MessageContent::ExternalRequest(req))
}

pub open spec fn built_in_controller_req_msg(rest_id: RestId, msg_content: MessageContent) -> Message {
    Message::form_msg(HostId::BuiltinController, HostId::ApiServer, rest_id, msg_content)
}

pub open spec fn resp_msg_matches_req_msg(resp_msg: Message, req_msg: Message) -> bool {
    ||| {
        &&& resp_msg.content.is_APIResponse()
        &&& req_msg.content.is_APIRequest()
        &&& resp_msg.dst == req_msg.src
        &&& resp_msg.src == req_msg.dst
        &&& resp_msg.rest_id == req_msg.rest_id
        &&& match resp_msg.content.get_APIResponse_0() {
            APIResponse::GetResponse(_) => req_msg.content.get_APIRequest_0().is_GetRequest(),
            APIResponse::ListResponse(_) => req_msg.content.get_APIRequest_0().is_ListRequest(),
            APIResponse::CreateResponse(_) => req_msg.content.get_APIRequest_0().is_CreateRequest(),
            APIResponse::DeleteResponse(_) => req_msg.content.get_APIRequest_0().is_DeleteRequest(),
            APIResponse::UpdateResponse(_) => req_msg.content.get_APIRequest_0().is_UpdateRequest(),
            APIResponse::UpdateStatusResponse(_) => req_msg.content.get_APIRequest_0().is_UpdateStatusRequest(),
        }
    }
    ||| {
        &&& resp_msg.content.is_ExternalResponse()
        &&& req_msg.content.is_ExternalRequest()
        &&& resp_msg.dst == req_msg.src
        &&& resp_msg.src == req_msg.dst
        &&& resp_msg.rest_id == req_msg.rest_id
    }
}

pub open spec fn form_matched_err_resp_msg(req_msg: Message, err: APIError) -> Message
    recommends req_msg.content.is_APIRequest(),
{
    match req_msg.content.get_APIRequest_0() {
        APIRequest::GetRequest(_) => Self::form_get_resp_msg(req_msg, GetResponse{res: Err(err)}),
        APIRequest::ListRequest(_) => Self::form_list_resp_msg(req_msg, ListResponse{res: Err(err)}),
        APIRequest::CreateRequest(_) => Self::form_create_resp_msg(req_msg, CreateResponse{res: Err(err)}),
        APIRequest::DeleteRequest(_) => Self::form_delete_resp_msg(req_msg, DeleteResponse{res: Err(err)}),
        APIRequest::UpdateRequest(_) => Self::form_update_resp_msg(req_msg, UpdateResponse{res: Err(err)}),
        APIRequest::UpdateStatusRequest(_) => Self::form_update_status_resp_msg(req_msg, UpdateStatusResponse{res: Err(err)}),
    }
}

pub open spec fn form_msg(src: HostId, dst: HostId, rest_id: RestId, msg_content: MessageContent) -> Message {
    Message {
        src: src,
        dst: dst,
        rest_id: rest_id,
        content: msg_content,
    }
}

pub open spec fn form_get_resp_msg(req_msg: Message, resp: GetResponse) -> Message
    recommends req_msg.content.is_get_request(),
{
    Self::form_msg(req_msg.dst, req_msg.src, req_msg.rest_id, MessageContent::APIResponse(APIResponse::GetResponse(resp)))
}

pub open spec fn form_list_resp_msg(req_msg: Message, resp: ListResponse) -> Message
    recommends req_msg.content.is_list_request(),
{
    Self::form_msg(req_msg.dst, req_msg.src, req_msg.rest_id, MessageContent::APIResponse(APIResponse::ListResponse(resp)))
}

pub open spec fn form_create_resp_msg(req_msg: Message, resp: CreateResponse) -> Message
    recommends req_msg.content.is_create_request(),
{
    Self::form_msg(req_msg.dst, req_msg.src, req_msg.rest_id, MessageContent::APIResponse(APIResponse::CreateResponse(resp)))
}

pub open spec fn form_delete_resp_msg(req_msg: Message, resp: DeleteResponse) -> Message
    recommends req_msg.content.is_delete_request(),
{
    Self::form_msg(req_msg.dst, req_msg.src, req_msg.rest_id, MessageContent::APIResponse(APIResponse::DeleteResponse(resp)))
}

pub open spec fn form_update_resp_msg(req_msg: Message, resp: UpdateResponse) -> Message
    recommends req_msg.content.is_update_request(),
{
    Self::form_msg(req_msg.dst, req_msg.src, req_msg.rest_id, MessageContent::APIResponse(APIResponse::UpdateResponse(resp)))
}

pub open spec fn form_update_status_resp_msg(req_msg: Message, resp: UpdateStatusResponse) -> Message
    recommends req_msg.content.is_update_request(),
{
    Self::form_msg(req_msg.dst, req_msg.src, req_msg.rest_id, MessageContent::APIResponse(APIResponse::UpdateStatusResponse(resp)))
}

pub open spec fn form_external_resp_msg(req_msg: Message, resp: ExternalMessageContent) -> Message
    recommends req_msg.content.is_ExternalRequest(),
{
    Self::form_msg(req_msg.dst, req_msg.src, req_msg.rest_id, MessageContent::ExternalResponse(resp))
}

pub open spec fn get_req_msg_content(key: ObjectRef) -> MessageContent {
    MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{
        key: key,
    }))
}

pub open spec fn list_req_msg_content(kind: Kind, namespace: StringView) -> MessageContent {
    MessageContent::APIRequest(APIRequest::ListRequest(ListRequest{
        kind: kind,
        namespace: namespace,
    }))
}

pub open spec fn create_req_msg_content(namespace: StringView, obj: DynamicObjectView) -> MessageContent {
    MessageContent::APIRequest(APIRequest::CreateRequest(CreateRequest{
        namespace: namespace,
        obj: obj,
    }))
}

pub open spec fn delete_req_msg_content(key: ObjectRef) -> MessageContent {
    MessageContent::APIRequest(APIRequest::DeleteRequest(DeleteRequest{
        key: key,
    }))
}

pub open spec fn update_req_msg_content(namespace: StringView, name: StringView, obj: DynamicObjectView) -> MessageContent {
    MessageContent::APIRequest(APIRequest::UpdateRequest(UpdateRequest{
        namespace: namespace,
        name: name,
        obj: obj,
    }))
}

pub open spec fn update_status_req_msg_content(namespace: StringView, name: StringView, obj: DynamicObjectView) -> MessageContent {
    MessageContent::APIRequest(APIRequest::UpdateStatusRequest(UpdateStatusRequest{
        namespace: namespace,
        name: name,
        obj: obj,
    }))
}

}

pub open spec fn api_request_msg_before(rest_id: RestId) -> spec_fn(Message) -> bool {
    |msg: Message| {
        &&& msg.rest_id < rest_id
        &&& {
            ||| msg.dst.is_ApiServer() && msg.content.is_APIRequest()
            ||| msg.dst.is_External() && msg.content.is_ExternalRequest()
        }
    }
}

pub open spec fn create_msg_for(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == key.namespace
        && msg.content.get_create_request().obj.kind == key.kind
        && msg.content.get_create_request().obj.metadata.name.is_Some()
        && msg.content.get_create_request().obj.metadata.name.get_Some_0() == key.name
}

pub open spec fn update_msg_for(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.content.is_update_request()
        && msg.content.get_update_request().key() == key
}

pub open spec fn update_status_msg_for(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.content.is_update_status_request()
        && msg.content.get_update_status_request().key() == key
}

pub open spec fn delete_msg_for(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.content.is_delete_request()
        && msg.content.get_delete_request().key == key
}

pub open spec fn update_status_msg_from_bc_for(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.src.is_BuiltinController()
        && msg.content.is_update_status_request()
        && msg.content.get_update_status_request().key() == key
}

pub open spec fn received_msg_destined_for(recv: Option<Message>, host_id: HostId) -> bool {
    if recv.is_Some() {
        recv.get_Some_0().dst == host_id
    } else {
        true
    }
}

pub open spec fn resource_get_request_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.content.is_get_request()
        && msg.content.get_get_request().key == key
}

pub open spec fn resource_create_request_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == key.namespace
        && msg.content.get_create_request().obj.metadata.name == Some(key.name)
        && msg.content.get_create_request().obj.kind == key.kind
}

// This is mainly used for reasoning about create requests with generate name
pub open spec fn resource_create_request_msg_without_name(kind: Kind, namespace: StringView) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == namespace
        && msg.content.get_create_request().obj.metadata.name.is_None()
        && msg.content.get_create_request().obj.metadata.generate_name.is_Some()
        && msg.content.get_create_request().obj.kind == kind
}

pub open spec fn resource_update_status_request_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.content.is_update_status_request()
        && msg.content.get_update_status_request().key() == key
}

pub open spec fn resource_update_request_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.content.is_update_request()
        && msg.content.get_update_request().key() == key
}

pub open spec fn resource_delete_request_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_ApiServer()
        && msg.content.is_delete_request()
        && msg.content.get_delete_request().key == key
}

}
