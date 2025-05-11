use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vstd_ext::string_view::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub type RPCId = nat;

pub type ExternalRequest = Value;

pub type ExternalResponse = Value;

pub struct MessageOps {
    pub recv: Option<Message>,
    pub send: Multiset<Message>,
}

pub struct Message {
    pub src: HostId,
    pub dst: HostId,
    pub rpc_id: RPCId,
    pub content: MessageContent,
}

#[is_variant]
pub enum HostId {
    APIServer,
    BuiltinController,
    Controller(int),
    External(int),
    PodMonkey,
}

// RPCIdAllocator allocates unique RPCId for each request sent by the controller.
// The API server state machine ensures the response will carry the same RPCId.
pub struct RPCIdAllocator {
    pub rpc_id_counter: RPCId,
}

impl RPCIdAllocator {
    // Allocate a RPCId which is the current rpc_id_counter
    // and also returns a new RPCIdAllocator with a different rpc_id_counter.
    //
    // The user (i.e., state machine) after allocating one RPCId, should use
    // the returned new RPCIdAllocator to allocate the next RPCId.
    // By doing so, the user of RPCIdAllocator always gets a RPCId
    // which differs from all the RPCIds allocated before because the
    // returned RPCIdAllocator has a incremented rpc_id_counter.
    //
    // Besides the uniqueness, the allocated RPCId can also serve as a timestamp
    // if we need to say some RPC messages are sent before the others.
    pub open spec fn allocate(self) -> (Self, RPCId) {
        (RPCIdAllocator {
            rpc_id_counter: self.rpc_id_counter + 1,
        }, self.rpc_id_counter)
    }
}

// Each MessageContent is a request/response.
#[is_variant]
pub enum MessageContent {
    APIRequest(APIRequest),
    APIResponse(APIResponse),
    ExternalRequest(ExternalRequest),
    ExternalResponse(ExternalResponse),
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

pub open spec fn controller_req_msg(controller_id: int, req_id: RPCId, req: APIRequest) -> Message {
    form_msg(HostId::Controller(controller_id), HostId::APIServer, req_id, MessageContent::APIRequest(req))
}

pub open spec fn controller_external_req_msg(controller_id: int, req_id: RPCId, req: ExternalRequest) -> Message {
    form_msg(HostId::Controller(controller_id), HostId::External(controller_id), req_id, MessageContent::ExternalRequest(req))
}

pub open spec fn built_in_controller_req_msg(rpc_id: RPCId, msg_content: MessageContent) -> Message {
    form_msg(HostId::BuiltinController, HostId::APIServer, rpc_id, msg_content)
}

pub open spec fn pod_monkey_req_msg(rpc_id: RPCId, msg_content: MessageContent) -> Message {
    form_msg(HostId::PodMonkey, HostId::APIServer, rpc_id, msg_content)
}

pub open spec fn resp_msg_matches_req_msg(resp_msg: Message, req_msg: Message) -> bool {
    ||| {
        &&& resp_msg.content.is_APIResponse()
        &&& req_msg.content.is_APIRequest()
        &&& resp_msg.dst == req_msg.src
        &&& resp_msg.src == req_msg.dst
        &&& resp_msg.rpc_id == req_msg.rpc_id
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
        &&& resp_msg.rpc_id == req_msg.rpc_id
    }
}

pub open spec fn form_matched_err_resp_msg(req_msg: Message, err: APIError) -> Message
    recommends req_msg.content.is_APIRequest(),
{
    match req_msg.content.get_APIRequest_0() {
        APIRequest::GetRequest(_) => form_get_resp_msg(req_msg, GetResponse{res: Err(err)}),
        APIRequest::ListRequest(_) => form_list_resp_msg(req_msg, ListResponse{res: Err(err)}),
        APIRequest::CreateRequest(_) => form_create_resp_msg(req_msg, CreateResponse{res: Err(err)}),
        APIRequest::DeleteRequest(_) => form_delete_resp_msg(req_msg, DeleteResponse{res: Err(err)}),
        APIRequest::UpdateRequest(_) => form_update_resp_msg(req_msg, UpdateResponse{res: Err(err)}),
        APIRequest::UpdateStatusRequest(_) => form_update_status_resp_msg(req_msg, UpdateStatusResponse{res: Err(err)}),
    }
}

pub open spec fn form_msg(src: HostId, dst: HostId, rpc_id: RPCId, msg_content: MessageContent) -> Message {
    Message {
        src: src,
        dst: dst,
        rpc_id: rpc_id,
        content: msg_content,
    }
}

pub open spec fn form_external_resp_msg(req_msg: Message, resp: ExternalResponse) -> Message
    recommends req_msg.content.is_ExternalRequest(),
{
    form_msg(req_msg.dst, req_msg.src, req_msg.rpc_id, MessageContent::ExternalResponse(resp))
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

pub open spec fn delete_req_msg_content(key: ObjectRef, preconditions: Option<PreconditionsView>) -> MessageContent {
    MessageContent::APIRequest(APIRequest::DeleteRequest(DeleteRequest{
        key: key,
        preconditions: preconditions,
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

pub open spec fn api_request_msg_before(rpc_id: RPCId) -> spec_fn(Message) -> bool {
    |msg: Message| {
        &&& msg.rpc_id < rpc_id
        &&& msg.dst.is_APIServer() && msg.content.is_APIRequest()
    }
}

pub open spec fn update_status_msg_from_bc_for(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_APIServer()
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
        msg.dst.is_APIServer()
        && msg.content.is_get_request()
        && msg.content.get_get_request().key == key
}

pub open spec fn resource_create_request_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_APIServer()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == key.namespace
        && msg.content.get_create_request().obj.metadata.name == Some(key.name)
        && msg.content.get_create_request().obj.kind == key.kind
}

// This is mainly used for reasoning about create requests with generate name
pub open spec fn resource_create_request_msg_without_name(kind: Kind, namespace: StringView) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_APIServer()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == namespace
        && msg.content.get_create_request().obj.metadata.name.is_None()
        && msg.content.get_create_request().obj.metadata.generate_name.is_Some()
        && msg.content.get_create_request().obj.kind == kind
}

pub open spec fn resource_update_status_request_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_APIServer()
        && msg.content.is_update_status_request()
        && msg.content.get_update_status_request().key() == key
}

pub open spec fn resource_update_request_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_APIServer()
        && msg.content.is_update_request()
        && msg.content.get_update_request().key() == key
}

pub open spec fn resource_delete_request_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.dst.is_APIServer()
        && msg.content.is_delete_request()
        && msg.content.get_delete_request().key == key
}

pub open spec fn is_ok_get_response_msg() -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.src.is_APIServer()
        && msg.content.is_get_response()
        && msg.content.get_get_response().res.is_Ok()
}

pub open spec fn is_ok_get_response_msg_and_matches_key(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        is_ok_get_response_msg()(msg)
        && msg.content.get_get_response().res.get_Ok_0().object_ref() == key
}

pub open spec fn is_ok_update_response_msg() -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.src.is_APIServer()
        && msg.content.is_update_response()
        && msg.content.get_update_response().res.is_Ok()
}

pub open spec fn is_ok_update_response_msg_and_matches_key(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        is_ok_update_response_msg()(msg)
        && msg.content.get_update_response().res.get_Ok_0().object_ref() == key
}

pub open spec fn is_ok_create_response_msg() -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.src.is_APIServer()
        && msg.content.is_create_response()
        && msg.content.get_create_response().res.is_Ok()
}

pub open spec fn is_ok_create_response_msg_and_matches_key(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        is_ok_create_response_msg()(msg)
        && msg.content.get_create_response().res.get_Ok_0().object_ref() == key
}

}

// Some handy (but repeated) functions generated using macro

macro_rules! declare_message_content_req_helper_methods {
    ($req_type:ty, $is_fun:ident, $get_fun:ident, $project:ident) => {
        verus! {
        impl MessageContent {
            pub open spec fn $is_fun(self) -> bool {
                &&& self is APIRequest
                &&& self.get_APIRequest_0() is $req_type
            }

            pub open spec fn $get_fun(self) -> $req_type {
                self.get_APIRequest_0().$project()
            }
        }
        }
    };
}

macro_rules! declare_message_content_req_helper_methods_with_key {
    ($req_type:ty, $is_fun:ident, $project:ident) => {
        verus! {
        impl MessageContent {
            pub open spec fn $is_fun(self, key: ObjectRef) -> bool {
                &&& self is APIRequest
                &&& self.get_APIRequest_0() is $req_type
                &&& self.get_APIRequest_0().$project().key() == key
            }
        }
        }
    };
}

macro_rules! declare_message_content_resp_helper_methods {
    ($resp_type:ty, $is_fun:ident, $get_fun:ident, $project:ident) => {
        verus! {
        impl MessageContent {
            pub open spec fn $is_fun(self) -> bool {
                &&& self is APIResponse
                &&& self.get_APIResponse_0() is $resp_type
            }

            pub open spec fn $get_fun(self) -> $resp_type {
                self.get_APIResponse_0().$project()
            }
        }
        }
    };
}

declare_message_content_req_helper_methods!(
    GetRequest,
    is_get_request,
    get_get_request,
    get_GetRequest_0
);

declare_message_content_req_helper_methods!(
    ListRequest,
    is_list_request,
    get_list_request,
    get_ListRequest_0
);

declare_message_content_req_helper_methods!(
    CreateRequest,
    is_create_request,
    get_create_request,
    get_CreateRequest_0
);

declare_message_content_req_helper_methods!(
    DeleteRequest,
    is_delete_request,
    get_delete_request,
    get_DeleteRequest_0
);

declare_message_content_req_helper_methods!(
    UpdateRequest,
    is_update_request,
    get_update_request,
    get_UpdateRequest_0
);

declare_message_content_req_helper_methods!(
    UpdateStatusRequest,
    is_update_status_request,
    get_update_status_request,
    get_UpdateStatusRequest_0
);

declare_message_content_req_helper_methods_with_key!(
    DeleteRequest,
    is_delete_request_with_key,
    get_DeleteRequest_0
);

declare_message_content_req_helper_methods_with_key!(
    UpdateRequest,
    is_update_request_with_key,
    get_UpdateRequest_0
);

declare_message_content_req_helper_methods_with_key!(
    UpdateStatusRequest,
    is_update_status_request_with_key,
    get_UpdateStatusRequest_0
);

declare_message_content_resp_helper_methods!(
    GetResponse,
    is_get_response,
    get_get_response,
    get_GetResponse_0
);

declare_message_content_resp_helper_methods!(
    ListResponse,
    is_list_response,
    get_list_response,
    get_ListResponse_0
);

declare_message_content_resp_helper_methods!(
    CreateResponse,
    is_create_response,
    get_create_response,
    get_CreateResponse_0
);

declare_message_content_resp_helper_methods!(
    DeleteResponse,
    is_delete_response,
    get_delete_response,
    get_DeleteResponse_0
);

declare_message_content_resp_helper_methods!(
    UpdateResponse,
    is_update_response,
    get_update_response,
    get_UpdateResponse_0
);

declare_message_content_resp_helper_methods!(
    UpdateStatusResponse,
    is_update_status_response,
    get_update_status_response,
    get_UpdateStatusResponse_0
);

macro_rules! declare_form_resp_msg_functions {
    ($resp_type:ty, $fun:ident) => {
        verus! {
        pub open spec fn $fun(req_msg: Message, resp: $resp_type) -> Message {
            form_msg(req_msg.dst, req_msg.src, req_msg.rpc_id, MessageContent::APIResponse(APIResponse::$resp_type(resp)))
        }
        }
    };
}

declare_form_resp_msg_functions!(GetResponse, form_get_resp_msg);

declare_form_resp_msg_functions!(ListResponse, form_list_resp_msg);

declare_form_resp_msg_functions!(CreateResponse, form_create_resp_msg);

declare_form_resp_msg_functions!(DeleteResponse, form_delete_resp_msg);

declare_form_resp_msg_functions!(UpdateResponse, form_update_resp_msg);

declare_form_resp_msg_functions!(UpdateStatusResponse, form_update_status_resp_msg);
