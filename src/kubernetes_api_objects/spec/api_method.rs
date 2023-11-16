// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::APIError;
use crate::kubernetes_api_objects::spec::{
    common::{Kind, ObjectRef},
    dynamic::*,
};
use crate::vstd_ext::string_view::*;
use vstd::string::*;
use vstd::{prelude::*, view::*};

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

}
