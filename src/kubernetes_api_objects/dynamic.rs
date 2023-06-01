// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
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
    pub fn from_kube(inner: K8SDynamicObject) -> DynamicObject {
        DynamicObject {
            inner: inner
        }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> K8SDynamicObject {
        self.inner
    }

    #[verifier(external)]
    pub fn kube_metadata_ref(&self) -> &K8SObjectMeta {
        &self.inner.metadata
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (obj: DynamicObject)
        ensures
            obj == self,
    {
        DynamicObject { inner: self.inner.clone() }
    }
}

/// DynamicObjectView is the ghost type of DynamicObject.
/// It is supposed to be used in spec and proof code.

pub struct DynamicObjectView {
    pub kind: Kind,
    pub metadata: ObjectMetaView,
    pub data: Value,
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
                namespace: Option::Some(namespace),
                ..self.metadata
            },
            ..self
        }
    }
}

}
