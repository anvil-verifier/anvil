// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
extern crate alloc;

use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::config_map::*;
use crate::kubernetes_api_objects::custom_resource::*;
use crate::kubernetes_api_objects::object::*;
use crate::pervasive::prelude::*;
use crate::pervasive::string::*;
use crate::pervasive_ext::string_view::*;

verus! {

// TODO: remove the redundant definitions in kubernetes_cluster::error and kubernetes_cluster::message

#[is_variant]
pub enum APIError {
    ObjectNotFound,
    ObjectAlreadyExists,
}

pub struct GetRequest {
    pub key: ObjectRef,
}

pub struct ListRequest {
    pub kind: Kind,
    pub namespace: StringView,
}

pub struct CreateRequest {
    pub obj: KubernetesObject,
}

pub struct DeleteRequest {
    pub key: ObjectRef,
}

#[is_variant]
pub enum APIRequest {
    GetRequest(GetRequest),
    ListRequest(ListRequest),
    CreateRequest(CreateRequest),
    DeleteRequest(DeleteRequest),
}

pub struct KubeGetRequest {
    pub name: String,
    pub namespace: String,
}

pub struct KubeListRequest {
    pub namespace: String,
}

// TODO: this K should be a trait that our k8s openapi wrapper types (e.g., ConfigMap) implement
pub struct KubeCreateRequest<#[verifier(maybe_negative)] K> {
    pub obj: K,
}

pub struct KubeDeleteRequest {
    pub name: String,
    pub namespace: String,
}

pub enum KubeCustomResourceRequest {
    GetRequest(KubeGetRequest),
    ListRequest(KubeListRequest),
    CreateRequest(KubeCreateRequest<CustomResource>),
    DeleteRequest(KubeDeleteRequest),
}

pub enum KubeConfigMapRequest {
    GetRequest(KubeGetRequest),
    ListRequest(KubeListRequest),
    CreateRequest(KubeCreateRequest<ConfigMap>),
    DeleteRequest(KubeDeleteRequest),
}

pub enum KubeAPIRequest {
    CustomResourceRequest(KubeCustomResourceRequest),
    ConfigMapRequest(KubeConfigMapRequest),
}

impl KubeAPIRequest {
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

pub struct GetResponse {
    pub res: Result<KubernetesObject, APIError>,
}

pub struct ListResponse {
    pub res: Result<Seq<KubernetesObject>, APIError>,
}

pub struct CreateResponse {
    pub res: Result<KubernetesObject, APIError>,
}

pub struct DeleteResponse {
    pub res: Result<KubernetesObject, APIError>,
}

#[is_variant]
pub enum APIResponse {
    GetResponse(GetResponse),
    ListResponse(ListResponse),
    CreateResponse(CreateResponse),
    DeleteResponse(DeleteResponse),
}

// TODO: work on Response types when we can import kube-rs types

// #[verifier(external_body)]
// pub struct KubeGetResponse {
//     // inner: Result<K> // Note that this should be kube_client::Result
// }

// #[verifier(external_body)]
// pub struct KubeListResponse {
//     // inner: Result<ObjectList<K>>
// }

// #[verifier(external_body)]
// pub struct KubeCreateResponse {
//     // inner: Result<K>
// }

// #[verifier(external_body)]
// pub struct KubeDeleteResponse {
//     // inner: Result<Either<K, Status>>
// }

// #[verifier(external_body)]
// pub enum KubeCustomResourceResponse {
//     GetResponse(KubeGetResponse),
//     ListResponse(KubeListResponse),
//     CreateResponse(KubeCreateResponse),
//     DeleteResponse(KubeDeleteResponse),
// }

// #[verifier(external_body)]
// pub enum KubeConfigMapResponse {
//     GetResponse(KubeGetResponse),
//     ListResponse(KubeListResponse),
//     CreateResponse(KubeCreateResponse),
//     DeleteResponse(KubeDeleteResponse),
// }

// #[verifier(external_body)]
// pub enum KubeAPIResponse {
//     CustomResourceResponse(KubeCustomResourceResponse),
//     ConfigMapResponse(KubeConfigMapResponse),
// }

}
