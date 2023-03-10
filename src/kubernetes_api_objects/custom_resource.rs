// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::pervasive::prelude::*;

verus! {

// TODO: CustomResource should be a generic type
#[verifier(external_body)]
pub struct CustomResource {
    // the content is specific to the controller
}

pub struct CustomResourceView {
    pub metadata: ObjectMetaView,
    pub spec: Option<CustomResourceSpecView>,
    pub status: Option<CustomResourceStatusView>,
}

impl CustomResource {
    pub spec fn view(&self) -> CustomResourceView;

    #[verifier(external_body)]
    pub fn default() -> (cr: CustomResource)
        ensures
            cr@.is_default(),
    {
        CustomResource {}
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
    }

    // is it OK to name it spec?
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

    pub open spec fn is_default(self) -> bool {
        &&& self.metadata.is_default()
        &&& self.spec.is_None()
        &&& self.status.is_None()
    }
}

#[verifier(external_body)]
pub struct CustomResourceSpec {
    // the content is specific to the controller
}

pub struct CustomResourceSpecView {
    // A lot more fields to specify...
}

impl CustomResourceSpec {
    pub spec fn view(&self) -> CustomResourceSpecView;

    #[verifier(external_body)]
    pub fn default() -> (cr_spec: CustomResourceSpec)
        ensures
            cr_spec@.is_default(),
    {
        CustomResourceSpec {}
    }
}

impl CustomResourceSpecView {
    pub open spec fn is_default(self) -> bool {
       true
       // The condition depends on how default() is implemented
    }
}

#[verifier(external_body)]
pub struct CustomResourceStatus {
    // the content is specific to the controller
}

pub struct CustomResourceStatusView {
    // A lot more fields to specify...
}

impl CustomResourceStatus {
    pub spec fn view(&self) -> CustomResourceStatusView;

    #[verifier(external_body)]
    pub fn default() -> (cr_status: CustomResourceStatus)
        ensures
            cr_status@.is_default(),
    {
        CustomResourceStatus {}
    }
}

impl CustomResourceStatusView {
    pub open spec fn is_default(self) -> bool {
       true
       // The condition depends on how default() is implemented
    }
}

}
