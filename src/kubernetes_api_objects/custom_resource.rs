// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

use deps_hack::SimpleCR;

verus! {

// TODO: CustomResource should be defined by the controller developer
#[verifier(external_body)]
pub struct CustomResource {
    inner: SimpleCR
}

pub struct CustomResourceView {
    pub metadata: ObjectMetaView,
    pub spec: Option<CustomResourceSpecView>,
    pub status: Option<CustomResourceStatusView>,
}

impl CustomResource {
    pub spec fn view(&self) -> CustomResourceView;

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::CustomResourceKind,
    {
        ApiResource::from_kube_api_resource(kube::api::ApiResource::erase::<SimpleCR>(&()))
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<CustomResourceSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn status(&self) -> (status: Option<CustomResourceStatus>)
        ensures
            self@.status.is_Some() == status.is_Some(),
            status.is_Some() ==> status.get_Some_0()@ == self@.status.get_Some_0(),
    {
        todo!()
    }
}

impl CustomResourceView {
    pub open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: self.kind(),
            metadata: self.metadata,
            data: Value::Object(Map::empty()
                                    .insert(spec_field(), if self.spec.is_None() {Value::Null} else {
                                        Value::Object(Map::empty().insert(spec_content_field(), Value::String(self.spec.get_Some_0().content)))
                                    })
                                    .insert(status_field(), if self.status.is_None() {Value::Null} else {
                                        Value::Object(Map::empty().insert(status_echoed_content_field(), Value::String(self.status.get_Some_0().echoed_content)))
                                    })
                                ),
        }
    }

    pub open spec fn from_dynamic_object(obj: DynamicObjectView) -> CustomResourceView {
        CustomResourceView {
            metadata: obj.metadata,
            spec: if obj.data.get_Object_0()[spec_field()].is_Null() {Option::None} else {Option::Some(CustomResourceSpecView{
                content: obj.data.get_Object_0()[spec_field()].get_Object_0()[spec_content_field()].get_String_0(),
            })},
            status: if obj.data.get_Object_0()[status_field()].is_Null() {Option::None} else {Option::Some(CustomResourceStatusView{
                echoed_content: obj.data.get_Object_0()[status_field()].get_Object_0()[status_echoed_content_field()].get_String_0(),
            })},
        }
    }

    pub proof fn integrity_check()
        ensures
            forall |o: CustomResourceView| o == CustomResourceView::from_dynamic_object(#[trigger] o.to_dynamic_object())
    {}

    pub open spec fn kind(self) -> Kind {
        Kind::CustomResourceKind
    }

    pub open spec fn object_ref(self) -> ObjectRef
        recommends
            self.metadata.name.is_Some(),
            self.metadata.namespace.is_Some(),
    {
        ObjectRef {
            kind: self.kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }
}

#[verifier(external_body)]
pub struct CustomResourceSpec {
    // TODO: add the content
}

pub struct CustomResourceSpecView {
    pub content: StringView,
}

impl CustomResourceSpec {
    pub spec fn view(&self) -> CustomResourceSpecView;
}

#[verifier(external_body)]
pub struct CustomResourceStatus {
    // TODO: add the content
}

pub struct CustomResourceStatusView {
    pub echoed_content: StringView,
}

impl CustomResourceStatus {
    pub spec fn view(&self) -> CustomResourceStatusView;
}

pub open spec fn spec_field() -> nat {0}

pub open spec fn status_field() -> nat {1}

pub open spec fn spec_content_field() -> nat {0}

pub open spec fn status_echoed_content_field() -> nat {0}

}
