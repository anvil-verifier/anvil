// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{object_meta::*, resource::*};
use crate::kubernetes_api_objects::spec::preconditions::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct Preconditions {
    inner: deps_hack::kube::api::Preconditions,
}

impl View for Preconditions {
    type V = PreconditionsView;

    spec fn view(&self) -> PreconditionsView;
}

impl std::clone::Clone for Preconditions {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Preconditions)
        ensures result@ == self@
    {
        Preconditions { inner: self.inner.clone() }
    }
}

impl Preconditions {
    #[verifier(external_body)]
    pub fn default() -> (preconditions: Preconditions)
        ensures preconditions@ == PreconditionsView::default(),
    {
        Preconditions { inner: deps_hack::kube::api::Preconditions::default() }
    }

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

implement_resource_wrapper_trait!(Preconditions, deps_hack::kube::api::Preconditions);
