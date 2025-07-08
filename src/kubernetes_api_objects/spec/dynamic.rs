// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::{common::*, object_meta::*, resource::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// DynamicObjectView is the ghost type of DynamicObject.


pub struct DynamicObjectView {
    pub kind: Kind,
    pub metadata: ObjectMetaView,
    pub spec: Value,
    pub status: Value,
}

impl DynamicObjectView {
    pub open spec fn object_ref(self) -> ObjectRef
        recommends
            self.metadata.name is Some,
            self.metadata.namespace is Some,
    {
        ObjectRef {
            kind: self.kind,
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> DynamicObjectView {
        DynamicObjectView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_name(self, name: StringView) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                name: Some(name),
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn with_namespace(self, namespace: StringView) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                namespace: Some(namespace),
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn with_resource_version(self, resource_version: ResourceVersion) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                resource_version: Some(resource_version),
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn with_uid(self, uid: Uid) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                uid: Some(uid),
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn with_deletion_timestamp(self, deletion_timestamp: StringView) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                deletion_timestamp: Some(deletion_timestamp),
                ..self.metadata
            },
            ..self
        }
    }
}

// This data type represents the entire cluster state that consists of
// many different objects in the form of DynamicObjectView
pub type StoredState = Map<ObjectRef, DynamicObjectView>;

}
