// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*,
    common::{Kind, ObjectRef},
    dynamic::*,
    error::*,
};
use crate::pervasive_ext::string_view::*;
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

/// KubeListRequest has the namespace to instantiate an Api.
///
/// Note that the kind is indicated by the upper layer Kube{ObjectKind}Request.

pub struct KubeListRequest {
    pub api_resource: ApiResource,
    pub namespace: String,
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

impl KubeAPIRequest {
    pub open spec fn to_view(&self) -> APIRequest {
        match self {
            KubeAPIRequest::GetRequest(get_req) => APIRequest::GetRequest(GetRequest {
                key: ObjectRef {
                    kind: get_req.api_resource@.kind,
                    name: get_req.name@,
                    namespace: get_req.namespace@,
                }
            }),
            KubeAPIRequest::ListRequest(list_req) => APIRequest::ListRequest(ListRequest {
                kind: list_req.api_resource@.kind,
                namespace: list_req.namespace@,
            }),
            KubeAPIRequest::CreateRequest(create_req) => APIRequest::CreateRequest(CreateRequest {
                namespace: create_req.namespace@,
                obj: create_req.obj@,
            }),
            KubeAPIRequest::DeleteRequest(delete_req) => APIRequest::DeleteRequest(DeleteRequest {
                key: ObjectRef {
                    kind: delete_req.api_resource@.kind,
                    name: delete_req.name@,
                    namespace: delete_req.namespace@,
                }
            }),
            KubeAPIRequest::UpdateRequest(update_req) => APIRequest::UpdateRequest(UpdateRequest {
                name: update_req.name@,
                namespace: update_req.namespace@,
                obj: update_req.obj@,
            }),
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

/// DeleteResponse has (last version of) the object deleted by DeleteRequest.

// TODO: need major revision here; DeleteResponse could be one of: (1) object is being deleted, (2) object is deleted, (3) error.
pub struct DeleteResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

/// UpdateResponse has the object updated by CreateRequest.

pub struct UpdateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

/// KubeAPIResponse represents API results used in executable.
///
/// KubeAPIResponse wraps around the results returned by the methods of kube::api::Api.

// TODO: implement all the variants after we import kube-rs.
#[is_variant]
pub enum KubeAPIResponse {
    GetResponse(KubeGetResponse),
    ListResponse(KubeListResponse),
    CreateResponse(KubeCreateResponse),
    DeleteResponse(KubeDeleteResponse),
    UpdateResponse(KubeUpdateResponse),
}

/// KubeGetResponse has the object returned by KubeGetRequest.

// TODO: We probably should just type define it as a Result, instead of having a struct wrapper.
pub struct KubeGetResponse {
    pub res: Result<DynamicObject, APIError>,
}

/// KubeListResponse has the sequence of objects returned by KubeListRequest.

pub struct KubeListResponse {
    pub res: Result<Vec<DynamicObject>, APIError>,
}

/// KubeCreateResponse has the object created by KubeCreateRequest.

pub struct KubeCreateResponse {
    pub res: Result<DynamicObject, APIError>,
}

/// DeleteResponse has (last version of) the object deleted by DeleteRequest.

// TODO: need major revision here; DeleteResponse could be one of: (1) object is being deleted, (2) object is deleted, (3) error.
pub struct KubeDeleteResponse {
    pub res: Result<DynamicObject, APIError>,
}

/// KubeUpdateResponse has the object updated by KubeUpdateRequest.

pub struct KubeUpdateResponse {
    pub res: Result<DynamicObject, APIError>,
}

pub open spec fn result_obj_to_view(res: Result<DynamicObject, APIError>) -> Result<DynamicObjectView, APIError> {
    match res {
        Ok(obj) => Ok(obj@),
        Err(err) => Err(err),
    }
}

pub open spec fn vec_obj_to_view(res: &Vec<DynamicObject>) -> Seq<DynamicObjectView> {
    Seq::empty() // TODO: construct the Seq that contains the view of each element in Vec
}

pub open spec fn result_objs_to_view(res: Result<Vec<DynamicObject>, APIError>) -> Result<Seq<DynamicObjectView>, APIError> {
    match res {
        Ok(objs) => Ok(vec_obj_to_view(&objs)),
        Err(err) => Err(err),
    }
}

impl KubeAPIResponse {
    /// to_view returns the view of KubeAPIResponse, i.e., APIResponse used for specifications.

    pub open spec fn to_view(&self) -> APIResponse {
        match self {
            KubeAPIResponse::GetResponse(get_resp) => APIResponse::GetResponse(GetResponse {
                res: result_obj_to_view(get_resp.res),
            }),
            KubeAPIResponse::ListResponse(list_resp) => APIResponse::ListResponse(ListResponse {
                res: result_objs_to_view(list_resp.res)
            }),
            KubeAPIResponse::CreateResponse(create_resp) => APIResponse::CreateResponse(CreateResponse {
                res: result_obj_to_view(create_resp.res),
            }),
            KubeAPIResponse::DeleteResponse(delete_resp) => APIResponse::DeleteResponse(DeleteResponse {
                res: result_obj_to_view(delete_resp.res),
            }),
            KubeAPIResponse::UpdateResponse(update_resp) => APIResponse::UpdateResponse(UpdateResponse {
                res: result_obj_to_view(update_resp.res),
            }),
        }
    }

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

}

pub open spec fn opt_resp_to_view(resp: &Option<KubeAPIResponse>) -> Option<APIResponse> {
    match resp {
        Some(resp) => Some(resp.to_view()),
        None => None,
    }
}

}
