// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::fluent_controller::fluentbit_config::spec::types::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, marshal::*, object_meta::*, owner_reference::*,
    resource::*, resource_requirements::*,
};
use crate::pervasive_ext::string_view::*;
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct FluentBitConfig {
    inner: deps_hack::FluentBitConfig
}

impl FluentBitConfig {
    pub spec fn view(&self) -> FluentBitConfigView;

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: FluentBitConfigSpec)
        ensures
            spec@ == self@.spec,
    {
        FluentBitConfigSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::FluentBitConfig {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == FluentBitConfigView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::FluentBitConfig>(&()))
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
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<FluentBitConfig, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == FluentBitConfigView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == FluentBitConfigView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::FluentBitConfig>();
        if parse_result.is_ok() {
            let res = FluentBitConfig { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::FluentBitConfig> for FluentBitConfig {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::FluentBitConfig) -> FluentBitConfig {
        FluentBitConfig {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::FluentBitConfig {
        self.inner
    }
}

#[verifier(external_body)]
pub struct FluentBitConfigSpec {
    inner: deps_hack::FluentBitConfigSpec,
}

impl FluentBitConfigSpec {
    pub spec fn view(&self) -> FluentBitConfigSpecView;

    #[verifier(external_body)]
    pub fn fluentbit_config(&self) -> (fluentbit_config: String)
        ensures
            fluentbit_config@ == self@.fluentbit_config,
    {
        String::from_rust_string(self.inner.fluentbit_config.to_string())
    }

    #[verifier(external_body)]
    pub fn parsers_config(&self) -> (parsers_config: String)
        ensures
            parsers_config@ == self@.parsers_config,
    {
        String::from_rust_string(self.inner.parsers_config.to_string())
    }
}

}
