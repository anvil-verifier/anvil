// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::exec::{api_resource::*, dynamic::*};
use crate::kubernetes_api_objects::spec::{
    api_method::*,
    common::{Kind, ObjectRef},
};
use crate::vstd_ext::string_view::*;
use vstd::{prelude::*, string::*, view::*};

use vstd::pervasive::unreached;

verus! {

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

impl View for KubeGetRequest {
    type V = GetRequest;
    open spec fn view(&self) -> GetRequest {
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

impl View for KubeListRequest {
    type V = ListRequest;
    open spec fn view(&self) -> ListRequest {
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

impl View for KubeCreateRequest {
    type V = CreateRequest;
    open spec fn view(&self) -> CreateRequest {
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

impl View for KubeDeleteRequest {
    type V = DeleteRequest;
    open spec fn view(&self) -> DeleteRequest {
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

impl View for KubeUpdateRequest {
    type V = UpdateRequest;
    open spec fn view(&self) -> UpdateRequest {
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

impl View for KubeUpdateStatusRequest {
    type V = UpdateStatusRequest;
    open spec fn view(&self) -> UpdateStatusRequest {
        UpdateStatusRequest {
            name: self.name@,
            namespace: self.namespace@,
            obj: self.obj@,
        }
    }
}

impl View for KubeAPIRequest {
    type V = APIRequest;

    open spec fn view(&self) -> APIRequest {
        match self {
            KubeAPIRequest::GetRequest(get_req) => APIRequest::GetRequest(get_req@),
            KubeAPIRequest::ListRequest(list_req) => APIRequest::ListRequest(list_req@),
            KubeAPIRequest::CreateRequest(create_req) => APIRequest::CreateRequest(create_req@),
            KubeAPIRequest::DeleteRequest(delete_req) => APIRequest::DeleteRequest(delete_req@),
            KubeAPIRequest::UpdateRequest(update_req) => APIRequest::UpdateRequest(update_req@),
            KubeAPIRequest::UpdateStatusRequest(update_status_req) => APIRequest::UpdateStatusRequest(update_status_req@),
        }
    }
}

pub open spec fn opt_req_to_view(req: &Option<KubeAPIRequest>) -> Option<APIRequest> {
    match req {
        Some(req) => Some(req@),
        None => None,
    }
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

impl View for KubeGetResponse {
    type V = GetResponse;
    open spec fn view(&self) -> GetResponse {
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

impl View for KubeListResponse {
    type V = ListResponse;
    open spec fn view(&self) -> ListResponse {
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

impl View for KubeCreateResponse {
    type V = CreateResponse;
    open spec fn view(&self) -> CreateResponse {
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

impl View for KubeDeleteResponse {
    type V = DeleteResponse;
    open spec fn view(&self) -> DeleteResponse {
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

impl View for KubeUpdateResponse {
    type V = UpdateResponse;
    open spec fn view(&self) -> UpdateResponse {
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

impl View for KubeUpdateStatusResponse {
    type V = UpdateStatusResponse;
    open spec fn view(&self) -> UpdateStatusResponse {
        match self.res {
            Ok(o) => UpdateStatusResponse { res: Ok(o@) },
            Err(e) => UpdateStatusResponse { res: Err(e) },
        }
    }
}

impl View for KubeAPIResponse {
    type V = APIResponse;
    open spec fn view(&self) -> APIResponse {
        match self {
            KubeAPIResponse::GetResponse(get_resp) => APIResponse::GetResponse(get_resp@),
            KubeAPIResponse::ListResponse(list_resp) => APIResponse::ListResponse(list_resp@),
            KubeAPIResponse::CreateResponse(create_resp) => APIResponse::CreateResponse(create_resp@),
            KubeAPIResponse::DeleteResponse(delete_resp) => APIResponse::DeleteResponse(delete_resp@),
            KubeAPIResponse::UpdateResponse(update_resp) => APIResponse::UpdateResponse(update_resp@),
            KubeAPIResponse::UpdateStatusResponse(update_status_resp) => APIResponse::UpdateStatusResponse(update_status_resp@),
        }
    }
}

impl KubeAPIResponse {
    pub fn is_get_response(&self) -> (res: bool)
        ensures
            res == self.is_GetResponse(),
    {
        match self {
            KubeAPIResponse::GetResponse(_) => true,
            _ => false,
        }
    }

    pub fn as_get_response_ref(&self) -> (resp: &KubeGetResponse)
        requires self.is_GetResponse(),
        ensures resp == self.get_GetResponse_0(),
    {
        match self {
            KubeAPIResponse::GetResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn into_get_response(self) -> (resp: KubeGetResponse)
        requires self.is_GetResponse(),
        ensures resp == self.get_GetResponse_0(),
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
            KubeAPIResponse::CreateResponse(_) => true,
            _ => false,
        }
    }

    pub fn as_create_response_ref(&self) -> (resp: &KubeCreateResponse)
        requires self.is_CreateResponse(),
        ensures resp == self.get_CreateResponse_0(),
    {
        match self {
            KubeAPIResponse::CreateResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn into_create_response(self) -> (resp: KubeCreateResponse)
        requires self.is_CreateResponse(),
        ensures resp == self.get_CreateResponse_0(),
    {
        match self {
            KubeAPIResponse::CreateResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn is_update_response(&self) -> (res: bool)
        ensures res == self.is_UpdateResponse(),
    {
        match self {
            KubeAPIResponse::UpdateResponse(_) => true,
            _ => false,
        }
    }

    pub fn as_update_response_ref(&self) -> (resp: &KubeUpdateResponse)
        requires self.is_UpdateResponse(),
        ensures resp == self.get_UpdateResponse_0(),
    {
        match self {
            KubeAPIResponse::UpdateResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn into_update_response(self) -> (resp: KubeUpdateResponse)
        requires self.is_UpdateResponse(),
        ensures resp == self.get_UpdateResponse_0(),
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
            KubeAPIResponse::UpdateStatusResponse(_) => true,
            _ => false,
        }
    }

    pub fn as_update_status_response_ref(&self) -> (resp: &KubeUpdateStatusResponse)
        requires self.is_UpdateStatusResponse(),
        ensures resp == self.get_UpdateStatusResponse_0(),
    {
        match self {
            KubeAPIResponse::UpdateStatusResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn into_update_status_response(self) -> (resp: KubeUpdateStatusResponse)
        requires self.is_UpdateStatusResponse(),
        ensures resp == self.get_UpdateStatusResponse_0(),
    {
        match self {
            KubeAPIResponse::UpdateStatusResponse(resp) => resp,
            _ => unreached(),
        }
    }
}

pub open spec fn opt_resp_to_view(resp: &Option<KubeAPIResponse>) -> Option<APIResponse> {
    match resp {
        Some(resp) => Some(resp@),
        None => None,
    }
}

}
