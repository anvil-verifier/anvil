// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::config_map::*;
use crate::kubernetes_api_objects::custom_resource::*;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::object::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;
use vstd::vec::Vec;

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
    pub obj: KubernetesObject,
}

/// DeleteRequest deletes the object with the key.

pub struct DeleteRequest {
    pub key: ObjectRef,
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
    CustomResourceRequest(KubeCustomResourceRequest),
    ConfigMapRequest(KubeConfigMapRequest),
}

/// KubeCustomResourceRequest represents all the requests concerning CustomResource.

pub enum KubeCustomResourceRequest {
    GetRequest(KubeGetRequest),
    ListRequest(KubeListRequest),
    CreateRequest(KubeCreateRequest<CustomResource>),
    DeleteRequest(KubeDeleteRequest),
}

/// KubeConfigMapRequest represents all the requests concerning ConfigMap.

pub enum KubeConfigMapRequest {
    GetRequest(KubeGetRequest),
    ListRequest(KubeListRequest),
    CreateRequest(KubeCreateRequest<ConfigMap>),
    DeleteRequest(KubeDeleteRequest),
}

/// KubeGetRequest has the name as the parameter of Api.get(), and namespace to instantiate an Api.

pub struct KubeGetRequest {
    pub name: String,
    pub namespace: String,
}

/// KubeListRequest has the namespace to instantiate an Api.
///
/// Note that the kind is indicated by the upper layer Kube{ObjectKind}Request.

pub struct KubeListRequest {
    pub namespace: String,
}

/// KubeCreateRequest has the obj as the parameter of Api.create().

pub struct KubeCreateRequest<#[verifier(maybe_negative)] K> {
    pub obj: K,
}

/// KubeDeleteRequest has the name as the parameter of Api.delete(), and namespace to instantiate an Api.

pub struct KubeDeleteRequest {
    pub name: String,
    pub namespace: String,
}

impl KubeAPIRequest {
    /// to_view returns the view of KubeAPIRequest, i.e., APIRequest used for specifications.
    ///
    /// We need verbose pattern matching here because we have one variant for each object kind.

    pub open spec fn to_view(&self) -> APIRequest {
        match self {
            KubeAPIRequest::CustomResourceRequest(req) => match req {
                KubeCustomResourceRequest::GetRequest(get_req) => APIRequest::GetRequest(GetRequest {
                    key: ObjectRef {
                        kind: Kind::CustomResourceKind,
                        name: get_req.name@,
                        namespace: get_req.namespace@,
                    }
                }),
                KubeCustomResourceRequest::ListRequest(list_req) => APIRequest::ListRequest(ListRequest {
                    kind: Kind::CustomResourceKind,
                    namespace: list_req.namespace@,
                }),
                KubeCustomResourceRequest::CreateRequest(create_req) => APIRequest::CreateRequest(CreateRequest {
                    obj: KubernetesObject::CustomResource(create_req.obj@),
                }),
                KubeCustomResourceRequest::DeleteRequest(delete_req) => APIRequest::DeleteRequest(DeleteRequest {
                    key: ObjectRef {
                        kind: Kind::CustomResourceKind,
                        name: delete_req.name@,
                        namespace: delete_req.namespace@,
                    }
                }),
            },
            KubeAPIRequest::ConfigMapRequest(req) => match req {
                KubeConfigMapRequest::GetRequest(get_req) => APIRequest::GetRequest(GetRequest {
                    key: ObjectRef {
                        kind: Kind::ConfigMapKind,
                        name: get_req.name@,
                        namespace: get_req.namespace@,
                    }
                }),
                KubeConfigMapRequest::ListRequest(list_req) => APIRequest::ListRequest(ListRequest {
                    kind: Kind::ConfigMapKind,
                    namespace: list_req.namespace@,
                }),
                KubeConfigMapRequest::CreateRequest(create_req) => APIRequest::CreateRequest(CreateRequest {
                    obj: KubernetesObject::ConfigMap(create_req.obj@),
                }),
                KubeConfigMapRequest::DeleteRequest(delete_req) => APIRequest::DeleteRequest(DeleteRequest {
                    key: ObjectRef {
                        kind: Kind::ConfigMapKind,
                        name: delete_req.name@,
                        namespace: delete_req.namespace@,
                    }
                }),
            },
        }
    }
}

pub open spec fn opt_req_to_view(req: &Option<KubeAPIRequest>) -> Option<APIRequest> {
    match req {
        Option::Some(req) => Option::Some(req.to_view()),
        Option::None => Option::None,
    }
}

/// APIResponse represents API responses sent from the Kubernetes API for specifications.

#[is_variant]
pub enum APIResponse {
    GetResponse(GetResponse),
    ListResponse(ListResponse),
    CreateResponse(CreateResponse),
    DeleteResponse(DeleteResponse),
}

/// GetResponse has the object returned by GetRequest.

pub struct GetResponse {
    pub res: Result<KubernetesObject, APIError>,
}

/// ListResponse has the sequence of objects returned by ListRequest.

pub struct ListResponse {
    pub res: Result<Seq<KubernetesObject>, APIError>,
}

/// CreateResponse has the object created by CreateRequest.

pub struct CreateResponse {
    pub res: Result<KubernetesObject, APIError>,
}

/// DeleteResponse has (last version of) the object deleted by DeleteRequest.

// TODO: need major revision here; DeleteResponse could be one of: (1) object is being deleted, (2) object is deleted, (3) error.
pub struct DeleteResponse {
    pub res: Result<KubernetesObject, APIError>,
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
}

/// KubeGetResponse has the object returned by KubeGetRequest.

pub struct KubeGetResponse {
    pub res: Result<KubeObject, APIError>,
}

/// KubeListResponse has the sequence of objects returned by KubeListRequest.

pub struct KubeListResponse {
    pub res: Result<Vec<KubeObject>, APIError>,
}

/// KubeCreateResponse has the object created by KubeCreateRequest.

pub struct KubeCreateResponse {
    pub res: Result<KubeObject, APIError>,
}

/// DeleteResponse has (last version of) the object deleted by DeleteRequest.

// TODO: need major revision here; DeleteResponse could be one of: (1) object is being deleted, (2) object is deleted, (3) error.
pub struct KubeDeleteResponse {
    pub res: Result<KubeObject, APIError>,
}

pub open spec fn result_obj_to_view(res: Result<KubeObject, APIError>) -> Result<KubernetesObject, APIError> {
    match res {
        Result::Ok(obj) => Result::Ok(obj.to_view()),
        Result::Err(err) => Result::Err(err),
    }
}

pub open spec fn vec_obj_to_view(res: &Vec<KubeObject>) -> Seq<KubernetesObject> {
    Seq::empty() // TODO: construct the Seq that contains the view of each element in Vec
}

pub open spec fn result_objs_to_view(res: Result<Vec<KubeObject>, APIError>) -> Result<Seq<KubernetesObject>, APIError> {
    match res {
        Result::Ok(objs) => Result::Ok(vec_obj_to_view(&objs)),
        Result::Err(err) => Result::Err(err),
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
        }
    }

    pub fn is_get_response(&self) -> (res: bool)
        ensures
            res <==> self.is_GetResponse(),
    {
        match self {
            KubeAPIResponse::GetResponse(resp) => true,
            _ => false,
        }
    }

    pub fn unwrap_get_response(self) -> (resp: KubeGetResponse)
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
}

pub open spec fn opt_resp_to_view(resp: &Option<KubeAPIResponse>) -> Option<APIResponse> {
    match resp {
        Option::Some(resp) => Option::Some(resp.to_view()),
        Option::None => Option::None,
    }
}

}
