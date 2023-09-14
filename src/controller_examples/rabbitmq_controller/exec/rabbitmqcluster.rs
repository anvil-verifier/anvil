// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, marshal::*, object_meta::*, owner_reference::*,
    resource::*,
};
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::spec::rabbitmqcluster::*;
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct RabbitmqCluster {
    inner: deps_hack::RabbitmqCluster
}

impl RabbitmqCluster {
    pub spec fn view(&self) -> RabbitmqClusterView;

    #[verifier(external_body)]
    pub fn name(&self) -> (name: Option<String>)
        ensures
            self@.name().is_Some() == name.is_Some(),
            name.is_Some() ==> name.get_Some_0()@ == self@.name().get_Some_0(),
    {
        match &self.inner.metadata.name {
            Some(n) => Some(String::from_rust_string(n.to_string())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn namespace(&self) -> (namespace: Option<String>)
        ensures
            self@.namespace().is_Some() == namespace.is_Some(),
            namespace.is_Some() ==> namespace.get_Some_0()@ == self@.namespace().get_Some_0(),
    {
        match &self.inner.metadata.namespace {
            Some(n) => Some(String::from_rust_string(n.to_string())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: RabbitmqClusterSpec)
        ensures
            spec@ == self@.spec,
    {
        RabbitmqClusterSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::RabbitmqCluster {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == RabbitmqClusterView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::RabbitmqCluster>(&()))
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
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<RabbitmqCluster, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == RabbitmqClusterView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == RabbitmqClusterView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::RabbitmqCluster>();
        if parse_result.is_ok() {
            let res = RabbitmqCluster { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::RabbitmqCluster> for RabbitmqCluster {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::RabbitmqCluster) -> RabbitmqCluster {
        RabbitmqCluster {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::RabbitmqCluster {
        self.inner
    }
}

#[verifier(external_body)]
pub struct RabbitmqClusterSpec {
    inner: deps_hack::RabbitmqClusterSpec,
}

impl RabbitmqClusterSpec {
    pub spec fn view(&self) -> RabbitmqClusterSpecView;

    #[verifier(external_body)]
    pub fn replicas(&self) -> (replicas: i32)
        ensures
            replicas as int == self@.replicas,
    {
        self.inner.replicas
    }

    #[verifier(external_body)]
    pub fn rabbitmq_config(&self) -> (rabbitmq_config: Option<RabbitmqConfig>)
        ensures
            self@.rabbitmq_config.is_Some() == rabbitmq_config.is_Some(),
            rabbitmq_config.is_Some() ==> rabbitmq_config.get_Some_0()@ == self@.rabbitmq_config.get_Some_0(),
    {
        match &self.inner.rabbitmq_config {
            Some(n) => Some(RabbitmqConfig { inner: n.clone()}),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn persistence(&self) -> (persistence: RabbitmqClusterPersistenceSpec)
        ensures
            persistence@ == self@.persistence,
    {
        RabbitmqClusterPersistenceSpec { inner: self.inner.persistence.clone() }
    }
}


#[verifier(external_body)]
pub struct RabbitmqConfig {
    inner: deps_hack::RabbitmqConfig,
}

impl RabbitmqConfig {
    pub spec fn view(&self) -> RabbitmqConfigView;

    #[verifier(external_body)]
    pub fn additional_config(&self) -> (additional_config: Option<String>)
        ensures
            self@.additional_config.is_Some() == additional_config.is_Some(),
            additional_config.is_Some() ==> additional_config.get_Some_0()@ == self@.additional_config.get_Some_0(),
    {
        match &self.inner.additional_config {
            Some(n) => Some(String::from_rust_string(n.to_string())),
            None => None,
        }
    }
}

#[verifier(external_body)]
pub struct RabbitmqClusterPersistenceSpec {
    inner: deps_hack::RabbitmqClusterPersistenceSpec,
}

impl RabbitmqClusterPersistenceSpec {
    pub spec fn view(&self) -> RabbitmqClusterPersistenceSpecView;

    #[verifier(external_body)]
    pub fn storage(&self) -> (storage: String)
        ensures
            storage@ == self@.storage,
    {
        String::from_rust_string(self.inner.storage.clone().0)
    }

    #[verifier(external_body)]
    pub fn storage_class_name(&self) -> (storage_class_name: String)
        ensures
            storage_class_name@ == self@.storage_class_name,
    {
        String::from_rust_string(self.inner.storage_class_name.clone())
    }
}

}
