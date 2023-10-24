// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::spec::types as spec_types;
use crate::fluent_controller::fluentbit::spec::types::{FluentBitSpecView, FluentBitView};
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::{
    affinity::*, api_resource::*, common::*, dynamic::*, marshal::*, object_meta::*,
    owner_reference::*, resource::*, resource_requirements::*, toleration::*,
};
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

pub struct FluentBitReconcileState {
    pub reconcile_step: FluentBitReconcileStep,
}

impl std::clone::Clone for FluentBitReconcileState {
    #[verifier(external_body)]
    fn clone(&self) -> (result: FluentBitReconcileState)
        ensures result == self
    {
        FluentBitReconcileState {
            reconcile_step: self.reconcile_step,
        }
    }
}

impl View for FluentBitReconcileState {
    type V = spec_types::FluentBitReconcileState;
    open spec fn view(&self) -> spec_types::FluentBitReconcileState {
        spec_types::FluentBitReconcileState {
            reconcile_step: self.reconcile_step,
        }
    }
}

#[verifier(external_body)]
pub struct FluentBit {
    inner: deps_hack::FluentBit
}

impl View for FluentBit {
    type V = spec_types::FluentBitView;

    spec fn view(&self) -> spec_types::FluentBitView;
}

impl FluentBit {
    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: FluentBitSpec)
        ensures
            spec@ == self@.spec,
    {
        FluentBitSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::FluentBit {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == FluentBitView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::FluentBit>(&()))
    }

    #[verifier(external_body)]
    pub fn controller_owner_ref(&self) -> (owner_reference: OwnerReference)
        ensures
            owner_reference@ == self@.controller_owner_ref(),
    {
        OwnerReference::from_kube(
            // We can safely unwrap here because the trait method implementation always returns a Some(...)
            self.inner.controller_owner_ref(&()).unwrap()
        )
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.marshal(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<FluentBit, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == FluentBitView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == FluentBitView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::FluentBit>();
        if parse_result.is_ok() {
            let res = FluentBit { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::FluentBit> for FluentBit {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::FluentBit) -> FluentBit {
        FluentBit {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::FluentBit {
        self.inner
    }
}

#[verifier(external_body)]
pub struct FluentBitSpec {
    inner: deps_hack::FluentBitSpec,
}

impl FluentBitSpec {
    pub spec fn view(&self) -> FluentBitSpecView;

    #[verifier(external_body)]
    pub fn fluentbit_config_name(&self) -> (fluentbit_config_name: String)
        ensures
            fluentbit_config_name@ == self@.fluentbit_config_name,
    {
        String::from_rust_string(self.inner.fluentbit_config_name.to_string())
    }

    #[verifier(external_body)]
    pub fn image(&self) -> (image: String)
        ensures
            image@ == self@.image,
    {
        String::from_rust_string(self.inner.image.clone())
    }

    #[verifier(external_body)]
    pub fn resources(&self) -> (resources: Option<ResourceRequirements>)
        ensures
            self@.resources.is_Some() == resources.is_Some(),
            resources.is_Some() ==> resources.get_Some_0()@ == self@.resources.get_Some_0(),
    {
        match &self.inner.resources {
            Some(r) => Some(ResourceRequirements::from_kube(r.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn tolerations(&self) -> (tolerations: Option<Vec<Toleration>>)
        ensures
            self@.tolerations.is_Some() == tolerations.is_Some(),
            tolerations.is_Some() ==> tolerations.get_Some_0()@.map_values(|t: Toleration| t@) == self@.tolerations.get_Some_0(),
    {
        match &self.inner.tolerations {
            Some(tols) => Some(tols.clone().into_iter().map(|t: deps_hack::k8s_openapi::api::core::v1::Toleration| Toleration::from_kube(t)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn labels(&self) -> (labels: StringMap)
        ensures
            labels@ == self@.labels,
    {
        StringMap::from_rust_map(self.inner.labels.clone())
    }

    #[verifier(external_body)]
    pub fn annotations(&self) -> (annotations: StringMap)
        ensures
            annotations@ == self@.annotations,
    {
        StringMap::from_rust_map(self.inner.annotations.clone())
    }

    #[verifier(external_body)]
    pub fn affinity(&self) -> (affinity: Option<Affinity>)
        ensures
            self@.affinity.is_Some() == affinity.is_Some(),
            affinity.is_Some() ==> affinity.get_Some_0()@ == self@.affinity.get_Some_0(),
    {
        match &self.inner.affinity {
            Some(a) => Some(Affinity::from_kube(a.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn node_selector(&self) -> (node_selector: StringMap)
        ensures
            node_selector@ == self@.node_selector,
    {
        StringMap::from_rust_map(self.inner.node_selector.clone())
    }

    #[verifier(external_body)]
    pub fn runtime_class_name(&self) -> (runtime_class_name: Option<String>)
        ensures
            opt_string_to_view(&runtime_class_name) == self@.runtime_class_name,
    {
        match &self.inner.runtime_class_name {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn dns_policy(&self) -> (dns_policy: Option<String>)
        ensures
            opt_string_to_view(&dns_policy) == self@.dns_policy,
    {
        match &self.inner.dns_policy {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn priority_class_name(&self) -> (priority_class_name: Option<String>)
        ensures
            opt_string_to_view(&priority_class_name) == self@.priority_class_name,
    {
        match &self.inner.priority_class_name {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn scheduler_name(&self) -> (scheduler_name: Option<String>)
        ensures
            opt_string_to_view(&scheduler_name) == self@.scheduler_name,
    {
        match &self.inner.scheduler_name {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }
}

}
