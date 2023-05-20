// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

use k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;

verus! {

#[verifier(external_body)]
pub struct ObjectMeta {
    inner: K8SObjectMeta,
}

pub struct ObjectMetaView {
    pub name: Option<StringView>,
    pub namespace: Option<StringView>,
    pub resource_version: Option<nat>, // make rv a nat so that it is easy to compare in spec/proof
    pub uid: Option<StringView>,
    pub deletion_timestamp: Option<StringView>,
    pub finalizers: Option<Seq<StringView>>,
    pub labels: Option<Map<StringView, StringView>>,
}

impl ObjectMeta {
    pub spec fn view(&self) -> ObjectMetaView;

    #[verifier(external_body)]
    pub fn default() -> (object_meta: ObjectMeta)
        ensures
            object_meta@ == ObjectMetaView::default(),
    {
        ObjectMeta {
            inner: K8SObjectMeta::default(),
        }
    }

    #[verifier(external)]
    pub fn from_kube_object_meta(inner: K8SObjectMeta) -> ObjectMeta {
        ObjectMeta {
            inner: inner
        }
    }

    #[verifier(external_body)]
    pub fn name(&self) -> (name: Option<String>)
        ensures
            self@.name.is_Some() == name.is_Some(),
            name.is_Some() ==> name.get_Some_0()@ == self@.name.get_Some_0(),
    {
        match &self.inner.name {
            std::option::Option::Some(n) => Option::Some(String::from_rust_string(n.to_string())),
            std::option::Option::None => Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = std::option::Option::Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn namespace(&self) -> (namespace: Option<String>)
        ensures
            self@.namespace.is_Some() == namespace.is_Some(),
            namespace.is_Some() ==> namespace.get_Some_0()@ == self@.namespace.get_Some_0(),
    {
        match &self.inner.namespace {
            std::option::Option::Some(n) => Option::Some(String::from_rust_string(n.to_string())),
            std::option::Option::None => Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures
            self@ == old(self)@.set_namespace(namespace@),
    {
        self.inner.namespace = std::option::Option::Some(namespace.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn labels(&self) -> (labels: Option<StringMap>)
        ensures
            self@.labels.is_Some() == labels.is_Some(),
            labels.is_Some() ==> labels.get_Some_0()@ == self@.labels.get_Some_0(),
    {
        match &self.inner.labels {
            std::option::Option::Some(n) => Option::Some(StringMap::from_rust_map(n.clone())),
            std::option::Option::None => Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn set_labels(&mut self, labels: StringMap)
        ensures
            self@ == old(self)@.set_labels(labels@),
    {
        self.inner.labels = std::option::Option::Some(labels.into_rust_map());
    }

    #[verifier(external_body)]
    pub fn resource_version(&self) -> (resource_version: Option<u64>)
        ensures
            self@.resource_version.is_Some() == resource_version.is_Some(),
            resource_version.is_Some() ==> resource_version.get_Some_0() as nat == self@.resource_version.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn uid(&self) -> (uid: Option<String>)
        ensures
            self@.uid.is_Some() == uid.is_Some(),
            uid.is_Some() ==> uid.get_Some_0()@ == self@.uid.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn deletion_timestamp(&self) -> (deletion_timestamp: Option<String>)
        ensures
            self@.deletion_timestamp.is_Some() == deletion_timestamp.is_Some(),
            deletion_timestamp.is_Some() ==> deletion_timestamp.get_Some_0()@ == self@.deletion_timestamp.get_Some_0(),
    {
        todo!()
    }

}

impl ObjectMetaView {
    pub open spec fn default() -> ObjectMetaView {
        ObjectMetaView {
            name: Option::None,
            namespace: Option::None,
            resource_version: Option::None,
            uid: Option::None,
            deletion_timestamp: Option::None,
            finalizers: Option::None,
            labels: Option::None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ObjectMetaView {
        ObjectMetaView {
            name: Option::Some(name),
            ..self
        }
    }

    pub open spec fn set_namespace(self, namespace: StringView) -> ObjectMetaView {
        ObjectMetaView {
            namespace: Option::Some(namespace),
            ..self
        }
    }

    pub open spec fn set_labels(self, labels: Map<StringView, StringView>) -> ObjectMetaView {
        ObjectMetaView {
            labels: Option::Some(labels),
            ..self
        }
    }
}

}
