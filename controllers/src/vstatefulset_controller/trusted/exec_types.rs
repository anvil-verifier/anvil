// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use verifiable_controllers::kubernetes_api_objects::error::UnmarshalError;
use verifiable_controllers::kubernetes_api_objects::exec::{
    api_resource::*, label_selector::*, persistent_volume_claim::*, pod_template_spec::*,
    prelude::*, resource::*,
};
use verifiable_controllers::kubernetes_api_objects::spec::{
    persistent_volume_claim::*, resource::*, volume_resource_requirements::*,
};
use crate::vstatefulset_controller::trusted::spec_types;
use verifiable_controllers::vstd_ext::{string_map::*, string_view::*};
use kube::Resource;
use vstd::prelude::*;

verus! {

implement_object_wrapper_type!(
    VStatefulSet,
    crate::crds::VStatefulSet,
    spec_types::VStatefulSetView
);

impl VStatefulSet {
    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: StatefulSetSpec)
        ensures spec@ == self@.spec,
    {
        StatefulSetSpec::from_kube(self.inner.spec.to_native())
    }

    // TODO: move controller_owner_ref to implement_object_wrapper_type
    #[verifier(external_body)]
    pub fn controller_owner_ref(&self) -> (owner_reference: OwnerReference)
        ensures owner_reference@ == self@.controller_owner_ref(),
    {
        // We can safely unwrap here because the trait method implementation always returns a Some(...)
        OwnerReference::from_kube(self.inner.controller_owner_ref(&()).unwrap())
    }
}

}
