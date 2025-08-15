// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{object_meta::*, resource::*};
use crate::kubernetes_api_objects::spec::preconditions::*;
use vstd::prelude::*;

verus! {

implement_field_wrapper_type!(
    Preconditions,
    deps_hack::kube::api::Preconditions,
    PreconditionsView
);

impl Preconditions {
    #[verifier(external_body)]
    pub fn set_uid_from_object_meta(&mut self, object_meta: ObjectMeta)
        ensures self@ == old(self)@.with_uid_from_object_meta(object_meta@),
    {
        self.inner.uid = object_meta.into_kube().uid;
    }

    #[verifier(external_body)]
    pub fn set_resource_version_from_object_meta(&mut self, object_meta: ObjectMeta)
        ensures self@ == old(self)@.with_resource_version_from_object_meta(object_meta@),
    {
        self.inner.resource_version = object_meta.into_kube().resource_version;
    }
}

}
