// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{common::*, marshal::*, object_meta::*, resource::*};
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

use deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;
use deps_hack::kube::api::DynamicObject as K8SDynamicObject;

verus! {

/// DynamicObject is mainly used to pass requests/response between reconcile_core and the shim layer.
/// We use DynamicObject in KubeAPIRequest and KubeAPIResponse so that they can carry the requests and responses
/// for all kinds of Kubernetes resource objects without exhaustive pattern matching.

#[verifier(external_body)]
pub struct DynamicObject {
    inner: K8SDynamicObject,
}

impl DynamicObject {
    pub spec fn view(&self) -> DynamicObjectView;

    #[verifier(external)]
    pub fn kube_metadata_ref(&self) -> &K8SObjectMeta {
        &self.inner.metadata
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (obj: DynamicObject)
        ensures
            obj == self,
    {
        DynamicObject { inner: self.inner.clone() }
    }
}

impl ResourceWrapper<K8SDynamicObject> for DynamicObject {
    #[verifier(external)]
    fn from_kube(inner: K8SDynamicObject) -> DynamicObject {
        DynamicObject {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> K8SDynamicObject {
        self.inner
    }
}

impl std::fmt::Debug for DynamicObject {
    #[verifier(external)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

/// DynamicObjectView is the ghost type of DynamicObject.
/// It is supposed to be used in spec and proof code.

pub struct DynamicObjectView {
    pub kind: Kind,
    pub metadata: ObjectMetaView,
    pub spec: Value,
    // TODO: add status, which will also be a Value
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

    pub open spec fn unset_deletion_timestamp(self) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                deletion_timestamp: None,
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn overwrite_deletion_timestamp(self, deletion_timestamp_opt: Option<StringView>) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                deletion_timestamp: deletion_timestamp_opt,
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
