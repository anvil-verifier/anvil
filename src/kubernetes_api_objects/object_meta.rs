// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::pervasive::prelude::*;
use crate::pervasive::string::*;
use crate::pervasive_ext::string_map;
use crate::pervasive_ext::StringView;

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

impl ObjectMetaView {

    pub open spec fn is_default(self) -> bool {
        &&& self.name.is_None()
        &&& self.namespace.is_None()
        &&& self.resource_version.is_None()
        &&& self.uid.is_None()
        &&& self.deletion_timestamp.is_None()
        &&& self.finalizers.is_None()
        &&& self.labels.is_None()
    }
}

impl ObjectMeta {
    pub spec fn view(&self) -> ObjectMetaView;

    #[verifier(external_body)]
    pub fn default() -> (object_meta: ObjectMeta)
        ensures
            object_meta@.is_default(),
    {
        ObjectMeta {
            inner: K8SObjectMeta::default(),
        }
    }

    #[verifier(external_body)]
    pub fn name(&self) -> (name: Option<String>)
        ensures
            self@.name.is_Some() == name.is_Some(),
            name.is_Some() ==> name.get_Some_0()@ == self@.name.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@.name.is_Some(),
            name@ == self@.name.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn namespace(&self) -> (namespace: Option<String>)
        ensures
            self@.namespace.is_Some() == namespace.is_Some(),
            namespace.is_Some() ==> namespace.get_Some_0()@ == self@.namespace.get_Some_0(),
    {
        todo!()
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

    // how to implement finalizers()?

    #[verifier(external_body)]
    pub fn labels(&self) -> (labels: Option<string_map::StringMap>)
        ensures
            self@.labels.is_Some() == labels.is_Some(),
            labels.is_Some() ==> labels.get_Some_0()@ == self@.labels.get_Some_0(),
    {
        todo!()
    }
}

}
