// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    affinity::*, api_resource::*, dynamic::*, object_meta::*, owner_reference::*, resource::*,
    resource_requirements::*, stateful_set::*, toleration::*,
};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::rabbitmq_controller::trusted::{spec_types, step::*};
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

// RabbitmqReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct RabbitmqReconcileState {
    // reconcile_step, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_step: RabbitmqReconcileStep,
    pub latest_config_map_rv_opt: Option<String>,
}

impl std::clone::Clone for RabbitmqReconcileState {

    #[verifier(external_body)]
    fn clone(&self) -> (result: RabbitmqReconcileState)
        ensures result == self
    {
        RabbitmqReconcileState {
            reconcile_step: self.reconcile_step,
            latest_config_map_rv_opt:
                match &self.latest_config_map_rv_opt {
                    Some(n) => Some(n.clone()),
                    None => None,
                }
        }
    }
}

impl View for RabbitmqReconcileState {
    type V = spec_types::RabbitmqReconcileState;

    open spec fn view(&self) -> spec_types::RabbitmqReconcileState {
        spec_types::RabbitmqReconcileState {
            reconcile_step: self.reconcile_step,
            latest_config_map_rv_opt:
                match self.latest_config_map_rv_opt {
                    Some(s) => Some(s@),
                    None => None,
                },
        }
    }
}

implement_custom_object_wrapper_type!(
    RabbitmqCluster,
    deps_hack::RabbitmqCluster,
    spec_types::RabbitmqClusterView
);

impl RabbitmqCluster {
    #[verifier(external_body)]
    pub fn well_formed(&self) -> (b: bool)
        ensures b == self@.well_formed(),
    {
        self.metadata().well_formed_for_namespaced()
        && self.state_validation()
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: RabbitmqClusterSpec)
        ensures spec@ == self@.spec,
    {
        RabbitmqClusterSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external_body)]
    pub fn state_validation(&self) -> (b: bool)
        ensures b == self@.state_validation()
    {
        self.inner.spec.replicas >= 0
    }
}

implement_view_trait!(
    RabbitmqClusterSpec,
    spec_types::RabbitmqClusterSpecView
);

#[verifier(external_body)]
pub struct RabbitmqClusterSpec {
    inner: deps_hack::RabbitmqClusterSpec,
}

impl RabbitmqClusterSpec {
    #[verifier(external_body)]
    pub fn replicas(&self) -> (replicas: i32)
        ensures replicas as int == self@.replicas,
    {
        self.inner.replicas
    }

    #[verifier(external_body)]
    pub fn image(&self) -> (image: String)
        ensures image@ == self@.image,
    {
        self.inner.image.clone()
    }

    #[verifier(external_body)]
    pub fn rabbitmq_config(&self) -> (rabbitmq_config: Option<RabbitmqConfig>)
        ensures
            self@.rabbitmq_config is Some == rabbitmq_config is Some,
            rabbitmq_config is Some ==> rabbitmq_config->0@ == self@.rabbitmq_config->0,
    {
        match &self.inner.rabbitmq_config {
            Some(n) => Some(RabbitmqConfig::from_kube(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn persistence(&self) -> (persistence: RabbitmqClusterPersistenceSpec)
        ensures persistence@ == self@.persistence,
    {
        RabbitmqClusterPersistenceSpec::from_kube(self.inner.persistence.clone())
    }

    #[verifier(external_body)]
    pub fn affinity(&self) -> (affinity: Option<Affinity>)
        ensures
            self@.affinity is Some == affinity is Some,
            affinity is Some ==> affinity->0@ == self@.affinity->0,
    {
        match &self.inner.affinity {
            Some(a) => Some(Affinity::from_kube(a.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn tolerations(&self) -> (tolerations: Option<Vec<Toleration>>)
        ensures
            self@.tolerations is Some == tolerations is Some,
            tolerations is Some ==> tolerations->0.deep_view() == self@.tolerations->0,
    {
        match &self.inner.tolerations {
            Some(tols) => Some(tols.clone().into_iter().map(|t: deps_hack::k8s_openapi::api::core::v1::Toleration| Toleration::from_kube(t)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn labels(&self) -> (labels: StringMap)
        ensures labels@ == self@.labels,
    {
        StringMap::from_rust_map(self.inner.labels.clone())
    }

    #[verifier(external_body)]
    pub fn annotations(&self) -> (annotations: StringMap)
        ensures annotations@ == self@.annotations,
    {
        StringMap::from_rust_map(self.inner.annotations.clone())
    }

    #[verifier(external_body)]
    pub fn resources(&self) -> (resources: Option<ResourceRequirements>)
        ensures
            self@.resources is Some == resources is Some,
            resources is Some ==> resources->0@ == self@.resources->0,
    {
        match &self.inner.resources {
            Some(res) => Some(ResourceRequirements::from_kube(res.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn pod_management_policy(&self) -> (policy: String)
        ensures policy@ == self@.pod_management_policy,
    {
        self.inner.pod_management_policy.clone()
    }

    #[verifier(external_body)]
    pub fn persistent_volume_claim_retention_policy(&self) -> (policy: Option<StatefulSetPersistentVolumeClaimRetentionPolicy>)
        ensures
            policy is Some == self@.persistent_volume_claim_retention_policy is Some,
            policy is Some ==> policy->0@ == self@.persistent_volume_claim_retention_policy->0,
    {
        match &self.inner.persistent_volume_claim_retention_policy {
            Some(n) => Some(StatefulSetPersistentVolumeClaimRetentionPolicy::from_kube(n.clone())),
            None => None,
        }
    }
}

implement_field_wrapper_type!(
    RabbitmqConfig,
    deps_hack::RabbitmqConfig,
    spec_types::RabbitmqConfigView
);

impl RabbitmqConfig {
    #[verifier(external_body)]
    pub fn additional_config(&self) -> (additional_config: Option<String>)
        ensures
            self@.additional_config is Some == additional_config is Some,
            additional_config is Some ==> additional_config->0@ == self@.additional_config->0,
    {
        self.inner.additional_config.clone()
    }

    #[verifier(external_body)]
    pub fn advanced_config(&self) -> (advanced_config: Option<String>)
        ensures
            self@.advanced_config is Some == advanced_config is Some,
            advanced_config is Some ==> advanced_config->0@ == self@.advanced_config->0,
    {
        self.inner.advanced_config.clone()
    }

    #[verifier(external_body)]
    pub fn env_config(&self) -> (env_config: Option<String>)
        ensures
            self@.env_config is Some == env_config is Some,
            env_config is Some ==> env_config->0@ == self@.env_config->0,
    {
        self.inner.env_config.clone()
    }
}

implement_field_wrapper_type!(
    RabbitmqClusterPersistenceSpec,
    deps_hack::RabbitmqClusterPersistenceSpec,
    spec_types::RabbitmqClusterPersistenceSpecView
);

impl RabbitmqClusterPersistenceSpec {
    #[verifier(external_body)]
    pub fn storage(&self) -> (storage: String)
        ensures storage@ == self@.storage,
    {
        self.inner.storage.clone().0
    }

    #[verifier(external_body)]
    pub fn storage_class_name(&self) -> (storage_class_name: String)
        ensures storage_class_name@ == self@.storage_class_name,
    {
        self.inner.storage_class_name.clone()
    }
}

#[verifier(external_body)]
pub fn random_encoded_string(data_len: usize) -> (cookie: String)
    ensures
        cookie@ == spec_types::random_encoded_string(data_len),
{
    let random_bytes: std::vec::Vec<std::primitive::u8> = (0..data_len).map(|_| deps_hack::rand::random::<std::primitive::u8>()).collect();
    deps_hack::base64::encode(random_bytes)
}

}
