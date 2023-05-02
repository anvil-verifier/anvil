// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

use k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;
use kube::api::DynamicObject as K8SDynamicObject;

verus! {

/// Value is used to "serialize" whatever Kubernetes resource object to a DynamicObject.
/// It looks similar to serde_json::Value but there are two major differences:
/// - Value::Object carries a Map<nat, Value>, while serde_json::Value::Object carries a Map<String, Value>
/// - Value has more variants for map structures like StringStringMap
///
/// All these differences are intended to make it easy (trivial) to prove a Kubernetes object
/// remains unchanged after "serialization" and "deserialization".
/// For example:
///     forall |o: ConfigMapView| o == ConfigMapView::from_dynamic_object(o.to_dynamic_object())
///
/// To do so, we try to avoid using StringView (Seq<Char>) as the key of Object Map because
/// Verus cannot easily tell two StringViews are different unless we reveal them.

#[is_variant]
pub enum Value {
    Null,
    Bool(bool),
    Nat(nat),
    Int(int),
    String(StringView),
    Array(Seq<Value>),
    StringStringMap(Map<StringView, StringView>),
    Object(Map<nat, Value>),
}

/// DynamicObject is mainly used to pass requests/response between reconcile_core and the shim layer.
/// We use DynamicObject in KubeAPIRequest and KubeAPIResponse so that they can carry the requests and responses
/// for all kinds of Kubernetes resource objects without exhaustive pattern matching.
/// Note that for each Kubernetes resource object we need to implement two methods:
/// - to_dynamic_object: converts a type K object to a DynamicObject
/// - from_dynamic_object: converts a DynamicObject to a type K object

#[verifier(external_body)]
pub struct DynamicObject {
    inner: K8SDynamicObject,
}

pub struct DynamicObjectView {
    pub kind: Kind,
    pub metadata: ObjectMetaView,
    pub data: Value,
}

impl DynamicObject {
    pub spec fn view(&self) -> DynamicObjectView;

    #[verifier(external)]
    pub fn from_kube_obj(inner: K8SDynamicObject) -> DynamicObject {
        DynamicObject {
            inner: inner
        }
    }

    #[verifier(external)]
    pub fn into_kube_obj(self) -> K8SDynamicObject {
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
}

}
