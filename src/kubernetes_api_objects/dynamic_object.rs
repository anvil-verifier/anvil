// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
use vstd::prelude::*;

use k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;
use kube::api::DynamicObject as K8SDynamicObject;

verus! {

#[verifier(external_body)]
pub struct DynamicObject {
    inner: K8SDynamicObject,
}

pub struct DynamicObjectView {
    pub metadata: ObjectMetaView,
    // TODO: implement data field
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

}

}
