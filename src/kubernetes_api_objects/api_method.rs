// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*,
    common::{Kind, ObjectRef},
    dynamic::*,
    error::*,
};
use crate::vstd_ext::{string_view::*, to_view::*};
use vstd::prelude::*;
use vstd::string::*;

use vstd::pervasive::unreached;

verus! {

/// APIRequest represents API requests sent to the Kubernetes API for specifications.
///
/// Kubernetes API accepts in general seven types requests: Get, List, Create, Delete, Update, Patch and Watch.
/// Each variant in APIRequest represents on type of request.
/// For now we do not consider Watch.

// TODO: implement Update and Patch request.
#[is_variant]
pub enum APIRequest {
    GetRequest(GetRequest),
    ListRequest(ListRequest),
    CreateRequest(CreateRequest),
    DeleteRequest(DeleteRequest),
    UpdateRequest(UpdateRequest),
    UpdateStatusRequest(UpdateStatusRequest),
}

/// GetRequest gets an object with the key (kind, name and namespace).

pub struct GetRequest {
    pub key: ObjectRef,
}

/// ListRequest lists all the objects of kind in namespace.

pub struct ListRequest {
    pub kind: Kind,
    pub namespace: StringView,
}

/// CreateRequest creates the obj.

pub struct CreateRequest {
    pub namespace: StringView,
    pub obj: DynamicObjectView,
}

impl CreateRequest {
    pub open spec fn key(self) -> ObjectRef {
        ObjectRef {
            name: self.obj.metadata.name.get_Some_0(),
            namespace: self.namespace,
            kind: self.obj.kind,
        }
    }
}

/// DeleteRequest deletes the object with the key.

pub struct DeleteRequest {
    pub key: ObjectRef,
}

/// UpdateRequest replaces the existing obj with a new one.

pub struct UpdateRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub obj: DynamicObjectView,
}

impl UpdateRequest {
    pub open spec fn key(self) -> ObjectRef {
        ObjectRef {
            kind: self.obj.kind,
            namespace: self.namespace,
            name: self.name,
        }
    }
}

/// UpdateStatusRequest replaces the status of the existing obj with a new one.

pub struct UpdateStatusRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub obj: DynamicObjectView,
}

impl UpdateStatusRequest {
    pub open spec fn key(self) -> ObjectRef {
        ObjectRef {
            kind: self.obj.kind,
            namespace: self.namespace,
            name: self.name,
        }
    }
}

/// KubeAPIRequest represents API requests used in executable.
///
/// kube-rs uses a generic type kube::api::Api as an api handle to send
/// requests to the Kubernetes API.
/// So KubeAPIRequest wraps around the variables used to instantiate kube::api::Api
/// and to call its methods.
///
/// Here we have one variant for each object kind because we need
/// the concrete object type to instantiate a kube::api::Api.
/// For example, to create a ConfigMap, we need to pass a ConfigMap object.

pub enum KubeAPIRequest {
    GetRequest(KubeGetRequest),
    ListRequest(KubeListRequest),
    CreateRequest(KubeCreateRequest),
    DeleteRequest(KubeDeleteRequest),
    UpdateRequest(KubeUpdateRequest),
    UpdateStatusRequest(KubeUpdateStatusRequest),
}

/// KubeGetRequest has the name as the parameter of Api.get(), and namespace to instantiate an Api.

pub struct KubeGetRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
}

impl KubeGetRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace.as_rust_string_ref(), self.name.as_rust_string_ref())
    }
}

impl ToView for KubeGetRequest {
    type V = GetRequest;
    open spec fn to_view(&self) -> GetRequest {
        GetRequest {
            key: ObjectRef {
                kind: self.api_resource@.kind,
                name: self.name@,
                namespace: self.namespace@,
            },
        }
    }
}

/// KubeListRequest has the namespace to instantiate an Api.
///
/// Note that the kind is indicated by the upper layer Kube{ObjectKind}Request.

pub struct KubeListRequest {
    pub api_resource: ApiResource,
    pub namespace: String,
}

impl KubeListRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}", self.api_resource.as_kube_ref().kind, self.namespace.as_rust_string_ref())
    }
}

impl ToView for KubeListRequest {
    type V = ListRequest;
    open spec fn to_view(&self) -> ListRequest {
        ListRequest {
            kind: self.api_resource@.kind,
            namespace: self.namespace@,
        }
    }
}

/// KubeCreateRequest has the obj as the parameter of Api.create().

pub struct KubeCreateRequest {
    pub api_resource: ApiResource,
    pub namespace: String,
    pub obj: DynamicObject,
}

impl KubeCreateRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace.as_rust_string_ref(), self.obj.kube_metadata_ref().name.as_ref().unwrap_or(&"".to_string()))
    }
}

impl ToView for KubeCreateRequest {
    type V = CreateRequest;
    open spec fn to_view(&self) -> CreateRequest {
        CreateRequest {
            namespace: self.namespace@,
            obj: self.obj@,
        }
    }
}

/// KubeDeleteRequest has the name as the parameter of Api.delete(), and namespace to instantiate an Api.

pub struct KubeDeleteRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
}

impl KubeDeleteRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace.as_rust_string_ref(), self.name.as_rust_string_ref())
    }
}

impl ToView for KubeDeleteRequest {
    type V = DeleteRequest;
    open spec fn to_view(&self) -> DeleteRequest {
        DeleteRequest {
            key: ObjectRef {
                kind: self.api_resource@.kind,
                name: self.name@,
                namespace: self.namespace@,
            }
        }
    }
}

/// KubeUpdateRequest has the obj as the parameter of Api.replace().

pub struct KubeUpdateRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub obj: DynamicObject,
}

impl KubeUpdateRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace.as_rust_string_ref(), self.name.as_rust_string_ref())
    }
}

impl ToView for KubeUpdateRequest {
    type V = UpdateRequest;
    open spec fn to_view(&self) -> UpdateRequest {
        UpdateRequest {
            name: self.name@,
            namespace: self.namespace@,
            obj: self.obj@,
        }
    }
}

/// KubeUpdateRequest has the obj as the parameter of Api.replace_status().

pub struct KubeUpdateStatusRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub obj: DynamicObject,
}

impl KubeUpdateStatusRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace.as_rust_string_ref(), self.name.as_rust_string_ref())
    }
}

impl ToView for KubeUpdateStatusRequest {
    type V = UpdateStatusRequest;
    open spec fn to_view(&self) -> UpdateStatusRequest {
        UpdateStatusRequest {
            name: self.name@,
            namespace: self.namespace@,
            obj: self.obj@,
        }
    }
}

impl KubeAPIRequest {
    pub open spec fn to_view(&self) -> APIRequest {
        match self {
            KubeAPIRequest::GetRequest(get_req) => APIRequest::GetRequest(get_req.to_view()),
            KubeAPIRequest::ListRequest(list_req) => APIRequest::ListRequest(list_req.to_view()),
            KubeAPIRequest::CreateRequest(create_req) => APIRequest::CreateRequest(create_req.to_view()),
            KubeAPIRequest::DeleteRequest(delete_req) => APIRequest::DeleteRequest(delete_req.to_view()),
            KubeAPIRequest::UpdateRequest(update_req) => APIRequest::UpdateRequest(update_req.to_view()),
            KubeAPIRequest::UpdateStatusRequest(update_status_req) => APIRequest::UpdateStatusRequest(update_status_req.to_view()),
        }
    }
}

pub open spec fn opt_req_to_view(req: &Option<KubeAPIRequest>) -> Option<APIRequest> {
    match req {
        Some(req) => Some(req.to_view()),
        None => None,
    }
}

/// APIResponse represents API responses sent from the Kubernetes API for specifications.

#[is_variant]
pub enum APIResponse {
    GetResponse(GetResponse),
    ListResponse(ListResponse),
    CreateResponse(CreateResponse),
    DeleteResponse(DeleteResponse),
    UpdateResponse(UpdateResponse),
    UpdateStatusResponse(UpdateStatusResponse),
}

/// GetResponse has the object returned by GetRequest.

pub struct GetResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

/// ListResponse has the sequence of objects returned by ListRequest.

pub struct ListResponse {
    pub res: Result<Seq<DynamicObjectView>, APIError>,
}

/// CreateResponse has the object created by CreateRequest.

pub struct CreateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

/// DeleteResponse does NOT contain the object that gets deleted.

pub struct DeleteResponse {
    pub res: Result<(), APIError>,
}

/// UpdateResponse has the object updated by UpdateRequest.

pub struct UpdateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

/// UpdateStatusResponse has the object updated by UpdateStatusRequest.

pub struct UpdateStatusResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

/// KubeAPIResponse represents API results used in executable.
///
/// KubeAPIResponse wraps around the results returned by the methods of kube::api::Api.

#[is_variant]
pub enum KubeAPIResponse {
    GetResponse(KubeGetResponse),
    ListResponse(KubeListResponse),
    CreateResponse(KubeCreateResponse),
    DeleteResponse(KubeDeleteResponse),
    UpdateResponse(KubeUpdateResponse),
    UpdateStatusResponse(KubeUpdateStatusResponse),
}

/// KubeGetResponse has the object returned by KubeGetRequest.

pub struct KubeGetResponse {
    pub res: Result<DynamicObject, APIError>,
}

impl ToView for KubeGetResponse {
    type V = GetResponse;
    open spec fn to_view(&self) -> GetResponse {
        match self.res {
            Ok(o) => GetResponse { res: Ok(o@) },
            Err(e) => GetResponse { res: Err(e) },
        }
    }
}

/// KubeListResponse has the sequence of objects returned by KubeListRequest.

pub struct KubeListResponse {
    pub res: Result<Vec<DynamicObject>, APIError>,
}

impl ToView for KubeListResponse {
    type V = ListResponse;
    open spec fn to_view(&self) -> ListResponse {
        match self.res {
            Ok(l) => ListResponse { res: Ok(l@.map_values(|o: DynamicObject| o@)) },
            Err(e) => ListResponse { res: Err(e) },
        }
    }
}

/// KubeCreateResponse has the object created by KubeCreateRequest.

pub struct KubeCreateResponse {
    pub res: Result<DynamicObject, APIError>,
}

impl ToView for KubeCreateResponse {
    type V = CreateResponse;
    open spec fn to_view(&self) -> CreateResponse {
        match self.res {
            Ok(o) => CreateResponse { res: Ok(o@) },
            Err(e) => CreateResponse { res: Err(e) },
        }
    }
}

/// DeleteResponse has (last version of) the object deleted by DeleteRequest.

pub struct KubeDeleteResponse {
    pub res: Result<(), APIError>,
}

impl ToView for KubeDeleteResponse {
    type V = DeleteResponse;
    open spec fn to_view(&self) -> DeleteResponse {
        match self.res {
            Ok(_) => DeleteResponse { res: Ok(()) },
            Err(e) => DeleteResponse { res: Err(e) },
        }
    }
}

/// KubeUpdateResponse has the object updated by KubeUpdateRequest.

pub struct KubeUpdateResponse {
    pub res: Result<DynamicObject, APIError>,
}

impl ToView for KubeUpdateResponse {
    type V = UpdateResponse;
    open spec fn to_view(&self) -> UpdateResponse {
        match self.res {
            Ok(o) => UpdateResponse { res: Ok(o@) },
            Err(e) => UpdateResponse { res: Err(e) },
        }
    }
}

/// KubeUpdateStatusResponse has the object updated by KubeUpdateStatusRequest.

pub struct KubeUpdateStatusResponse {
    pub res: Result<DynamicObject, APIError>,
}

impl ToView for KubeUpdateStatusResponse {
    type V = UpdateStatusResponse;
    open spec fn to_view(&self) -> UpdateStatusResponse {
        match self.res {
            Ok(o) => UpdateStatusResponse { res: Ok(o@) },
            Err(e) => UpdateStatusResponse { res: Err(e) },
        }
    }
}

impl ToView for KubeAPIResponse {
    type V = APIResponse;
    open spec fn to_view(&self) -> APIResponse {
        match self {
            KubeAPIResponse::GetResponse(get_resp) => APIResponse::GetResponse(get_resp.to_view()),
            KubeAPIResponse::ListResponse(list_resp) => APIResponse::ListResponse(list_resp.to_view()),
            KubeAPIResponse::CreateResponse(create_resp) => APIResponse::CreateResponse(create_resp.to_view()),
            KubeAPIResponse::DeleteResponse(delete_resp) => APIResponse::DeleteResponse(delete_resp.to_view()),
            KubeAPIResponse::UpdateResponse(update_resp) => APIResponse::UpdateResponse(update_resp.to_view()),
            KubeAPIResponse::UpdateStatusResponse(update_status_resp) => APIResponse::UpdateStatusResponse(update_status_resp.to_view()),
        }
    }
}

impl KubeAPIResponse {
    pub fn is_get_response(&self) -> (res: bool)
        ensures
            res == self.is_GetResponse(),
    {
        match self {
            KubeAPIResponse::GetResponse(resp) => true,
            _ => false,
        }
    }

    pub fn as_get_response_ref(&self) -> (resp: &KubeGetResponse)
        requires
            self.is_GetResponse(),
        ensures
            resp == self.get_GetResponse_0(),
    {
        match self {
            KubeAPIResponse::GetResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn into_get_response(self) -> (resp: KubeGetResponse)
        requires
            self.is_GetResponse(),
        ensures
            resp == self.get_GetResponse_0(),
    {
        match self {
            KubeAPIResponse::GetResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn is_create_response(&self) -> (res: bool)
        ensures
            res == self.is_CreateResponse(),
    {
        match self {
            KubeAPIResponse::CreateResponse(resp) => true,
            _ => false,
        }
    }

    pub fn as_create_response_ref(&self) -> (resp: &KubeCreateResponse)
        requires
            self.is_CreateResponse(),
        ensures
            resp == self.get_CreateResponse_0(),
    {
        match self {
            KubeAPIResponse::CreateResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn into_create_response(self) -> (resp: KubeCreateResponse)
        requires
            self.is_CreateResponse(),
        ensures
            resp == self.get_CreateResponse_0(),
    {
        match self {
            KubeAPIResponse::CreateResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn is_update_response(&self) -> (res: bool)
        ensures
            res == self.is_UpdateResponse(),
    {
        match self {
            KubeAPIResponse::UpdateResponse(resp) => true,
            _ => false,
        }
    }

    pub fn as_update_response_ref(&self) -> (resp: &KubeUpdateResponse)
        requires
            self.is_UpdateResponse(),
        ensures
            resp == self.get_UpdateResponse_0(),
    {
        match self {
            KubeAPIResponse::UpdateResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn into_update_response(self) -> (resp: KubeUpdateResponse)
        requires
            self.is_UpdateResponse(),
        ensures
            resp == self.get_UpdateResponse_0(),
    {
        match self {
            KubeAPIResponse::UpdateResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn is_update_status_response(&self) -> (res: bool)
        ensures
            res == self.is_UpdateStatusResponse(),
    {
        match self {
            KubeAPIResponse::UpdateStatusResponse(resp) => true,
            _ => false,
        }
    }

    pub fn as_update_status_response_ref(&self) -> (resp: &KubeUpdateStatusResponse)
        requires
            self.is_UpdateStatusResponse(),
        ensures
            resp == self.get_UpdateStatusResponse_0(),
    {
        match self {
            KubeAPIResponse::UpdateStatusResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn into_update_status_response(self) -> (resp: KubeUpdateStatusResponse)
        requires
            self.is_UpdateStatusResponse(),
        ensures
            resp == self.get_UpdateStatusResponse_0(),
    {
        match self {
            KubeAPIResponse::UpdateStatusResponse(resp) => resp,
            _ => unreached(),
        }
    }
}

pub open spec fn opt_resp_to_view(resp: &Option<KubeAPIResponse>) -> Option<APIResponse> {
    match resp {
        Some(resp) => Some(resp.to_view()),
        None => None,
    }
}

}
