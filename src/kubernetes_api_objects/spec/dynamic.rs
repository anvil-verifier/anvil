// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::{
    common::*, marshal::*, object_meta::*, owner_reference::*, resource::*,
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

/// DynamicObjectView is the ghost type of DynamicObject.
/// It is supposed to be used in spec and proof code.

pub struct DynamicObjectView {
    pub kind: Kind,
    pub metadata: ObjectMetaView,
    pub spec: Value,
    pub status: Value,
}

impl DynamicObjectView {
    pub open spec fn object_ref(self) -> ObjectRef
        recommends
            self.metadata.name.is_Some(),
            self.metadata.namespace.is_Some(),
    {
        ObjectRef {
            kind: self.kind,
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> DynamicObjectView {
        DynamicObjectView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                name: Some(name),
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn set_namespace(self, namespace: StringView) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                namespace: Some(namespace),
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn set_resource_version(self, resource_version: ResourceVersion) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                resource_version: Some(resource_version),
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn set_uid(self, uid: Uid) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                uid: Some(uid),
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn set_deletion_timestamp(self, deletion_timestamp: StringView) -> DynamicObjectView {
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
