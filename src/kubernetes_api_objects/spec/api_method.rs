// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::APIError;
use crate::kubernetes_api_objects::spec::{
    common::{Kind, ObjectRef},
    dynamic::*,
    owner_reference::*,
    preconditions::*,
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// APIRequest represents API requests sent to the Kubernetes API for specifications.
//
// Kubernetes API accepts in general seven types requests: Get, List, Create, Delete, Update, Patch and Watch.
// Each variant in APIRequest represents on type of request.
// For now we do not consider Watch.

// TODO: implement Update and Patch request.
#[is_variant_no_deprecation_warning]
pub enum APIRequest {
    GetRequest(GetRequest),
    ListRequest(ListRequest),
    CreateRequest(CreateRequest),
    DeleteRequest(DeleteRequest),
    UpdateRequest(UpdateRequest),
    UpdateStatusRequest(UpdateStatusRequest),
    GetThenDeleteRequest(GetThenDeleteRequest),
    GetThenUpdateRequest(GetThenUpdateRequest),
}

// GetRequest gets an object with the key (kind, name and namespace).

pub struct GetRequest {
    pub key: ObjectRef,
}

impl GetRequest {
    pub open spec fn key(self) -> ObjectRef {
        self.key
    }
}

// ListRequest lists all the objects of kind in namespace.

pub struct ListRequest {
    pub kind: Kind,
    pub namespace: StringView,
}

// CreateRequest creates the obj.

pub struct CreateRequest {
    pub namespace: StringView,
    pub obj: DynamicObjectView,
}

impl CreateRequest {
    // Note: it's possible for name to be None and generate_name is used instead.
    pub open spec fn key(self) -> ObjectRef {
        ObjectRef {
            name: self.obj.metadata.name->0,
            namespace: self.namespace,
            kind: self.obj.kind,
        }
    }
}

// DeleteRequest deletes the object with the key.

pub struct DeleteRequest {
    pub key: ObjectRef,
    pub preconditions: Option<PreconditionsView>,
}

impl DeleteRequest {
    pub open spec fn key(self) -> ObjectRef {
        self.key
    }
}

// UpdateRequest replaces the existing obj with a new one.
// TODO: remove name/namespace as they should always be consistent with the object in payload

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

// UpdateStatusRequest replaces the status of the existing obj with a new one.

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

// GetThenDeleteRequest deletes the object with the key only when it's owned by owner_ref and avoids conflicts caused by
// version race.
//
// TODO: GetThenUpdateRequest should carry a spec_fn(DynamicObjectView) -> bool
// TODO: Add a type invariant by #[verifier::type_invariant].
//       Skipped because it requires fields to be private, and Deref is not supported so we have to add getter/setter

pub struct GetThenDeleteRequest {
    pub key: ObjectRef,
    pub owner_ref: OwnerReferenceView,
}

impl GetThenDeleteRequest {
    pub open spec fn key(self) -> ObjectRef {
        self.key
    }

    pub open spec fn well_formed(self) -> bool {
        self.owner_ref.controller is Some
        && self.owner_ref.controller->0
    }
}

// GetThenUpdateRequest replaces the existing obj with a new one only when it's owned by owner_ref and avoids
// conflicts caused by version race.
//
// TODO: GetThenUpdateRequest should carry a spec_fn(DynamicObjectView) -> Option<DynamicObjectView>
// TODO: remove name/namespace as they should always be consistent with the object in payload

pub struct GetThenUpdateRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub owner_ref: OwnerReferenceView,
    pub obj: DynamicObjectView,
}

impl GetThenUpdateRequest {
    pub open spec fn key(self) -> ObjectRef {
        ObjectRef {
            kind: self.obj.kind,
            namespace: self.namespace,
            name: self.name,
        }
    }

    pub open spec fn well_formed(self) -> bool {
        self.owner_ref.controller is Some
        && self.owner_ref.controller->0
    }
}

// APIResponse represents API responses sent from the Kubernetes API for specifications.

#[is_variant_no_deprecation_warning]
pub enum APIResponse {
    GetResponse(GetResponse),
    ListResponse(ListResponse),
    CreateResponse(CreateResponse),
    DeleteResponse(DeleteResponse),
    UpdateResponse(UpdateResponse),
    UpdateStatusResponse(UpdateStatusResponse),
    GetThenDeleteResponse(GetThenDeleteResponse),
    GetThenUpdateResponse(GetThenUpdateResponse),
}

// GetResponse has the object returned by GetRequest.

pub struct GetResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

// ListResponse has the sequence of objects returned by ListRequest.

pub struct ListResponse {
    pub res: Result<Seq<DynamicObjectView>, APIError>,
}

// CreateResponse has the object created by CreateRequest.

pub struct CreateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

// DeleteResponse does NOT contain the object that gets deleted.

pub struct DeleteResponse {
    pub res: Result<(), APIError>,
}

// UpdateResponse has the object updated by UpdateRequest.

pub struct UpdateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

// UpdateStatusResponse has the object updated by UpdateStatusRequest.

pub struct UpdateStatusResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

// GetThenUpdateResponse has the object updated by GetThenUpdateRequest.

pub struct GetThenUpdateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

// GetThenDeleteResponse does NOT contain the object that gets deleted.

pub struct GetThenDeleteResponse {
    pub res: Result<(), APIError>,
}

}
