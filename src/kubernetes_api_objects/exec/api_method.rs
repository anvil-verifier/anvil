// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, owner_reference::*, preconditions::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{api_method::*, common::ObjectRef};
use vstd::prelude::*;

use vstd::pervasive::unreached;

verus! {

// KubeAPIRequest represents API requests used in executable.
//
// kube-rs uses a generic type kube::api::Api as an api handle to send
// requests to the Kubernetes API.
// So KubeAPIRequest wraps around the variables used to instantiate kube::api::Api
// and to call its methods.
//
// Here we have one variant for each object kind because we need
// the concrete object type to instantiate a kube::api::Api.
// For example, to create a ConfigMap, we need to pass a ConfigMap object.

pub enum KubeAPIRequest {
    GetRequest(KubeGetRequest),
    ListRequest(KubeListRequest),
    CreateRequest(KubeCreateRequest),
    DeleteRequest(KubeDeleteRequest),
    UpdateRequest(KubeUpdateRequest),
    UpdateStatusRequest(KubeUpdateStatusRequest),
    GetThenDeleteRequest(KubeGetThenDeleteRequest),
    GetThenUpdateRequest(KubeGetThenUpdateRequest),
}

// KubeGetRequest has the name as the parameter of Api.get(), and namespace to instantiate an Api.

pub struct KubeGetRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
}

impl KubeGetRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace, self.name)
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

// KubeListRequest has the namespace to instantiate an Api.

pub struct KubeListRequest {
    pub api_resource: ApiResource,
    pub namespace: String,
}

impl KubeListRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}", self.api_resource.as_kube_ref().kind, self.namespace)
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

// KubeCreateRequest has the obj as the parameter of Api.create().

pub struct KubeCreateRequest {
    pub api_resource: ApiResource,
    pub namespace: String,
    pub obj: DynamicObject,
}

impl KubeCreateRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace, self.obj.as_kube_ref().metadata.name.as_ref().unwrap_or(&"".to_string()))
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

// KubeDeleteRequest has the name as the parameter of Api.delete(), and namespace to instantiate an Api.

pub struct KubeDeleteRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub preconditions: Option<Preconditions>,
}

impl KubeDeleteRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace, self.name)
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
            },
            preconditions: self.preconditions.deep_view(),
        }
    }
}

// KubeUpdateRequest has the obj as the parameter of Api.replace().

pub struct KubeUpdateRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub obj: DynamicObject,
}

impl KubeUpdateRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace, self.name)
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

// KubeUpdateRequest has the obj as the parameter of Api.replace_status().

pub struct KubeUpdateStatusRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub obj: DynamicObject,
}

impl KubeUpdateStatusRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace, self.name)
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

// KubeGetThenDeleteRequest has the name as the parameter of Api.get() and Api.delete(), and namespace to instantiate an Api.
//
// TODO: KubeGetThenDeleteRequest should carry a Box<dyn Fn(DynamicObject) -> bool> when Verus supports dyn

pub struct KubeGetThenDeleteRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub owner_ref: OwnerReference,
}

impl KubeGetThenDeleteRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace, self.name)
    }

    pub fn well_formed(&self) -> (res: bool)
        ensures
            res == self@.well_formed(),
    {
        self.owner_ref.controller().is_some() && self.owner_ref.controller().unwrap()
    }
}

impl View for KubeGetThenDeleteRequest {
    type V = GetThenDeleteRequest;
    open spec fn view(&self) -> GetThenDeleteRequest {
        GetThenDeleteRequest {
            key: ObjectRef {
                kind: self.api_resource@.kind,
                name: self.name@,
                namespace: self.namespace@,
            },
            owner_ref: self.owner_ref@,
        }
    }
}

// KubeGetThenUpdateRequest has the name as the parameter of Api.get() and the obj as the parameter of Api.replace().
//
// TODO: KubeGetThenUpdateRequest should carry a Box<dyn Fn(DynamicObject) -> Option<DynamicObject>> when Verus supports dyn

pub struct KubeGetThenUpdateRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub owner_ref: OwnerReference,
    pub obj: DynamicObject,
}

impl KubeGetThenUpdateRequest {
    #[verifier(external)]
    pub fn key(&self) -> std::string::String {
        format!("{}/{}/{}", self.api_resource.as_kube_ref().kind, self.namespace, self.name)
    }

    pub fn well_formed(&self) -> (res: bool)
        ensures
            res == self@.well_formed(),
    {
        self.owner_ref.controller().is_some() && self.owner_ref.controller().unwrap()
    }
}

impl View for KubeGetThenUpdateRequest {
    type V = GetThenUpdateRequest;
    open spec fn view(&self) -> GetThenUpdateRequest {
        GetThenUpdateRequest {
            name: self.name@,
            namespace: self.namespace@,
            owner_ref: self.owner_ref@,
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
            KubeAPIRequest::GetThenDeleteRequest(req) => APIRequest::GetThenDeleteRequest(req@),
            KubeAPIRequest::GetThenUpdateRequest(req) => APIRequest::GetThenUpdateRequest(req@),
        }
    }
}

impl DeepView for KubeAPIRequest {
    type V = APIRequest;

    open spec fn deep_view(&self) -> APIRequest {
        self@
    }
}

// KubeAPIResponse represents API results used in executable.
//
// KubeAPIResponse wraps around the results returned by the methods of kube::api::Api.

pub enum KubeAPIResponse {
    GetResponse(KubeGetResponse),
    ListResponse(KubeListResponse),
    CreateResponse(KubeCreateResponse),
    DeleteResponse(KubeDeleteResponse),
    UpdateResponse(KubeUpdateResponse),
    UpdateStatusResponse(KubeUpdateStatusResponse),
    GetThenDeleteResponse(KubeGetThenDeleteResponse),
    GetThenUpdateResponse(KubeGetThenUpdateResponse),
}

// KubeGetResponse has the object returned by KubeGetRequest.

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

// KubeListResponse has the sequence of objects returned by KubeListRequest.

pub struct KubeListResponse {
    pub res: Result<Vec<DynamicObject>, APIError>,
}

impl View for KubeListResponse {
    type V = ListResponse;
    open spec fn view(&self) -> ListResponse {
        match self.res {
            Ok(l) => ListResponse { res: Ok(l.deep_view()) },
            Err(e) => ListResponse { res: Err(e) },
        }
    }
}

// KubeCreateResponse has the object created by KubeCreateRequest.

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

// KubeDeleteResponse does NOT have the object.

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

// KubeUpdateResponse has the object updated by KubeUpdateRequest.

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

// KubeUpdateStatusResponse has the object updated by KubeUpdateStatusRequest.

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

// KubeGetThenUpdateResponse has the object updated by KubeGetThenUpdateRequest.

pub struct KubeGetThenUpdateResponse {
    pub res: Result<DynamicObject, APIError>,
}

impl View for KubeGetThenUpdateResponse {
    type V = GetThenUpdateResponse;
    open spec fn view(&self) -> GetThenUpdateResponse {
        match self.res {
            Ok(o) => GetThenUpdateResponse { res: Ok(o@) },
            Err(e) => GetThenUpdateResponse { res: Err(e) },
        }
    }
}

// KubeGetThenDeleteResponse does NOT have the object.

pub struct KubeGetThenDeleteResponse {
    pub res: Result<(), APIError>,
}

impl View for KubeGetThenDeleteResponse {
    type V = GetThenDeleteResponse;
    open spec fn view(&self) -> GetThenDeleteResponse {
        match self.res {
            Ok(_) => GetThenDeleteResponse { res: Ok(()) },
            Err(e) => GetThenDeleteResponse { res: Err(e) },
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
            KubeAPIResponse::GetThenDeleteResponse(resp) => APIResponse::GetThenDeleteResponse(resp@),
            KubeAPIResponse::GetThenUpdateResponse(resp) => APIResponse::GetThenUpdateResponse(resp@),
        }
    }
}

}

macro_rules! declare_kube_api_response_helper_methods {
    ($is_fun:ident, $as_ref_fun:ident, $into_fun:ident, $resp_type:ty, $kube_resp_type:ty, $project:ident) => {
        verus! {

        impl KubeAPIResponse {
            pub fn $is_fun(&self) -> (res: bool)
                ensures res == self is $resp_type,
            {
                match self {
                    KubeAPIResponse::$resp_type(_) => true,
                    _ => false,
                }
            }

            pub fn $as_ref_fun(&self) -> (resp: &$kube_resp_type)
                requires self is $resp_type,
                ensures resp == self.$project(),
            {
                match self {
                    KubeAPIResponse::$resp_type(resp) => resp,
                    _ => unreached(),
                }
            }

            pub fn $into_fun(self) -> (resp: $kube_resp_type)
                requires self is $resp_type,
                ensures resp == self.$project(),
            {
                match self {
                    KubeAPIResponse::$resp_type(resp) => resp,
                    _ => unreached(),
                }
            }
        }

        }
    };
}

declare_kube_api_response_helper_methods!(
    is_get_response,
    as_get_response_ref,
    into_get_response,
    GetResponse,
    KubeGetResponse,
    get_GetResponse_0
);

declare_kube_api_response_helper_methods!(
    is_list_response,
    as_list_response_ref,
    into_list_response,
    ListResponse,
    KubeListResponse,
    get_ListResponse_0
);

declare_kube_api_response_helper_methods!(
    is_create_response,
    as_create_response_ref,
    into_create_response,
    CreateResponse,
    KubeCreateResponse,
    get_CreateResponse_0
);

declare_kube_api_response_helper_methods!(
    is_delete_response,
    as_delete_response_ref,
    into_delete_response,
    DeleteResponse,
    KubeDeleteResponse,
    get_DeleteResponse_0
);

declare_kube_api_response_helper_methods!(
    is_update_response,
    as_update_response_ref,
    into_update_response,
    UpdateResponse,
    KubeUpdateResponse,
    get_UpdateResponse_0
);

declare_kube_api_response_helper_methods!(
    is_update_status_response,
    as_update_response_status_ref,
    into_update_status_response,
    UpdateStatusResponse,
    KubeUpdateStatusResponse,
    get_UpdateStatusResponse_0
);

declare_kube_api_response_helper_methods!(
    is_get_then_update_response,
    as_get_then_update_response_ref,
    into_get_then_update_response,
    GetThenUpdateResponse,
    KubeGetThenUpdateResponse,
    get_GetThenUpdateResponse_0
);

declare_kube_api_response_helper_methods!(
    is_get_then_delete_response,
    as_get_then_delete_response_ref,
    into_get_then_delete_response,
    GetThenDeleteResponse,
    KubeGetThenDeleteResponse,
    get_GetThenDeleteResponse_0
);
