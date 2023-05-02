// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

use k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;
use kube::api::DynamicObject as K8SDynamicObject;

verus! {

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
