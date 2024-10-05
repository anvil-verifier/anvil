// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, label_selector::*, pod_template_spec::*, prelude::*,
};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::vdeployment_controller::trusted::{spec_types, step::*};
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct VDeployment {
    inner: deps_hack::VDeployment
}

impl View for VDeployment {
    type V = spec_types::VDeploymentView;

    spec fn view(&self) -> spec_types::VDeploymentView;
}

impl VDeployment {
    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: VDeploymentSpec)
        ensures spec@ == self@.spec,
    {
        VDeploymentSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == spec_types::VDeploymentView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::VDeployment>(&()))
    }

    #[verifier(external_body)]
    pub fn controller_owner_ref(&self) -> (owner_reference: OwnerReference)
        ensures owner_reference@ == self@.controller_owner_ref(),
    {
        // We can safely unwrap here because the trait method implementation always returns a Some(...)
        OwnerReference::from_kube(self.inner.controller_owner_ref(&()).unwrap())
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<VDeployment, UnmarshalError>)
        ensures
            res.is_Ok() == spec_types::VDeploymentView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == spec_types::VDeploymentView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::VDeployment>();
        if parse_result.is_ok() {
            let res = VDeployment { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(())
        }
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::VDeployment> for VDeployment {
    fn from_kube(inner: deps_hack::VDeployment) -> VDeployment { VDeployment { inner: inner } }

    fn into_kube(self) -> deps_hack::VDeployment { self.inner }
}

#[verifier(external_body)]
pub struct VDeploymentSpec {
    inner: deps_hack::VDeploymentSpec,
}

impl VDeploymentSpec {
    pub spec fn view(&self) -> spec_types::VDeploymentSpecView;

    #[verifier(external_body)]
    pub fn replicas(&self) -> (replicas: Option<i32>)
        ensures
            replicas.is_Some() == self@.replicas.is_Some(),
            replicas.is_Some() ==> replicas.get_Some_0() as int == self@.replicas.get_Some_0(),
    {
        self.inner.replicas
    }

    #[verifier(external_body)]
    pub fn selector(&self) -> (selector: LabelSelector)
        ensures selector@ == self@.selector
    {
        LabelSelector::from_kube(self.inner.selector.clone())
    }

    #[verifier(external_body)]
    pub fn template(&self) -> (template: Option<PodTemplateSpec>)
        ensures
            template.is_Some() == self@.template.is_Some(),
            template.is_Some() ==> template.get_Some_0()@ == self@.template.get_Some_0(),
    {
        match &self.inner.template {
            Some(t) => Some(PodTemplateSpec::from_kube(t.clone())),
            None => None
        }
    }
}

}
