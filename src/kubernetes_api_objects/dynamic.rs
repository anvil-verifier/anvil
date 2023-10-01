// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    common::*, marshal::*, object_meta::*, owner_reference::*, resource::*,
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

/// DynamicObject is mainly used to pass requests/response between reconcile_core and the shim layer.
/// We use DynamicObject in KubeAPIRequest and KubeAPIResponse so that they can carry the requests and responses
/// for all kinds of Kubernetes resource objects without exhaustive pattern matching.

#[verifier(external_body)]
pub struct DynamicObject {
    inner: deps_hack::kube::api::DynamicObject,
}

impl View for DynamicObject {
    type V = DynamicObjectView;

    spec fn view(&self) -> DynamicObjectView;
}

impl DynamicObject {
    #[verifier(external)]
    pub fn kube_metadata_ref(&self) -> &deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
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

impl ResourceWrapper<deps_hack::kube::api::DynamicObject> for DynamicObject {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::kube::api::DynamicObject) -> DynamicObject {
        DynamicObject {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::kube::api::DynamicObject {
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
    pub status: Value,
}

/// DynamicObjectMutView includes the fields of a core object that can be
/// mutated by a custom controller, including labels, annotations, owner_references, finalizers and spec.
/// Things like resource version and uid are not here because they are either decided
/// by the api server/etcd, or cannot be mutated by the controller once the object gets created.
///
/// Note that we do not include status here because this type is designed for create and update requests,
/// not update-status request.

pub struct DynamicObjectMutView {
    pub labels: Option<Map<StringView, StringView>>,
    pub annotations: Option<Map<StringView, StringView>>,
    pub owner_references: Option<Seq<OwnerReferenceView>>,
    pub finalizers: Option<Seq<StringView>>,
    pub spec: Value,
}

pub type DynamicObjectMutViewPred = FnSpec(DynamicObjectMutView) -> bool;

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

    pub open spec fn mutable_subset(self) -> DynamicObjectMutView {
        DynamicObjectMutView {
            labels: self.metadata.labels,
            annotations: self.metadata.annotations,
            owner_references: self.metadata.owner_references,
            finalizers: self.metadata.finalizers,
            spec: self.spec,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> DynamicObjectView {
        DynamicObjectView {
            metadata: metadata,
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
