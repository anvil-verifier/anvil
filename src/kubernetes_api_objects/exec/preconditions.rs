// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{object_meta::*, resource::*};
use crate::kubernetes_api_objects::spec::preconditions::*;
use crate::vstd_ext::string_view::*;
use vstd::{prelude::*, string::*, view::*};

verus! {

#[verifier(external_body)]
pub struct Preconditions {
    inner: deps_hack::kube::api::Preconditions,
}

impl Preconditions {
    pub spec fn view(&self) -> PreconditionsView;

    #[verifier(external_body)]
    pub fn default() -> (preconditions: Preconditions)
        ensures preconditions@ == PreconditionsView::default(),
    {
        Preconditions { inner: deps_hack::kube::api::Preconditions::default() }
    }

    #[verifier(external_body)]
    pub fn set_uid_from_object_meta(&mut self, object_meta: ObjectMeta)
        ensures self@ == old(self)@.set_uid_from_object_meta(object_meta@),
    {
        self.inner.uid = object_meta.into_kube().uid;
    }

    #[verifier(external_body)]
    pub fn set_resource_version_from_object_meta(&mut self, object_meta: ObjectMeta)
        ensures self@ == old(self)@.set_resource_version_from_object_meta(object_meta@),
    {
        self.inner.resource_version = object_meta.into_kube().resource_version;
    }

    #[verifier(external)]
    fn from_kube(inner: deps_hack::kube::api::Preconditions) -> Preconditions { Preconditions { inner: inner } }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::kube::api::Preconditions { self.inner }
}

}
