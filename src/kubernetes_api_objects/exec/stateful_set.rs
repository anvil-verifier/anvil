// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, label_selector::*, object_meta::*, persistent_volume_claim::*,
    pod_template_spec::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{resource::*, stateful_set::*};
use vstd::prelude::*;

// StatefulSet is a type of API object used for managing stateful applications,
// mainly a group of Pods and PersistentVolumeClaims attached to the Pods.
// A StatefulSet object allows different types of Volumes attached to the pods,
// including ConfigMaps, Secrets and PersistentVolumeClaims.
// It also exposes the applications using a headless service.
//
// This definition is a wrapper of StatefulSet defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/apps/v1/stateful_set.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/concepts/workloads/controllers/statefulset/.

implement_object_wrapper_type!(
    StatefulSet,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSet,
    StatefulSetView
);

verus! {

impl StatefulSet {
    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<StatefulSetSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        if self.inner.spec.is_none() {
            None
        } else {
            Some(StatefulSetSpec::from_kube(self.inner.spec.as_ref().unwrap().clone()))
        }
    }

    #[verifier(external_body)]
    pub fn status(&self) -> (status: Option<StatefulSetStatus>)
        ensures
            self@.status.is_Some() == status.is_Some(),
            status.is_Some() ==> status.get_Some_0()@ == self@.status.get_Some_0(),
    {
        if self.inner.status.is_none() {
            None
        } else {
            Some(StatefulSetStatus::from_kube(self.inner.status.as_ref().unwrap().clone()))
        }
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: StatefulSetSpec)
        ensures self@ == old(self)@.with_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }
}

#[verifier(external_body)]
pub struct StatefulSetSpec {
    inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec,
}

impl StatefulSetSpec {
    pub uninterp spec fn view(&self) -> StatefulSetSpecView;

    #[verifier(external_body)]
    pub fn default() -> (stateful_set_spec: StatefulSetSpec)
        ensures stateful_set_spec@ == StatefulSetSpecView::default(),
    {
        StatefulSetSpec { inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        StatefulSetSpec { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_replicas(&mut self, replicas: i32)
        ensures self@ == old(self)@.with_replicas(replicas as int),
    {
        self.inner.replicas = Some(replicas)
    }

    #[verifier(external_body)]
    pub fn set_selector(&mut self, selector: LabelSelector)
        ensures self@ == old(self)@.with_selector(selector@),
    {
        self.inner.selector = selector.into_kube()
    }

    #[verifier(external_body)]
    pub fn set_service_name(&mut self, service_name: String)
        ensures self@ == old(self)@.with_service_name(service_name@),
    {
        self.inner.service_name = service_name
    }

    #[verifier(external_body)]
    pub fn set_template(&mut self, template: PodTemplateSpec)
        ensures self@ == old(self)@.with_template(template@),
    {
        self.inner.template = template.into_kube()
    }

    #[verifier(external_body)]
    pub fn set_volume_claim_templates(&mut self, volume_claim_templates: Vec<PersistentVolumeClaim>)
        ensures self@ == old(self)@.with_volume_claim_templates(volume_claim_templates@.map_values(|pvc: PersistentVolumeClaim| pvc@)),
    {
        self.inner.volume_claim_templates = Some(
            volume_claim_templates.into_iter().map(|pvc: PersistentVolumeClaim| pvc.into_kube()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_pod_management_policy(&mut self, pod_management_policy: String)
        ensures self@ == old(self)@.with_pod_management_policy(pod_management_policy@),
    {
        self.inner.pod_management_policy = Some(pod_management_policy)
    }

    #[verifier(external_body)]
    pub fn set_pvc_retention_policy(&mut self, pvc_retention_policy: StatefulSetPersistentVolumeClaimRetentionPolicy)
        ensures self@ == old(self)@.with_pvc_retention_policy(pvc_retention_policy@),
    {
        self.inner.persistent_volume_claim_retention_policy = Some(pvc_retention_policy.into_kube())
    }

    #[verifier(external_body)]
    pub fn unset_pvc_retention_policy(&mut self)
        ensures self@ == old(self)@.without_pvc_retention_policy(),
    {
        self.inner.persistent_volume_claim_retention_policy = None
    }

    #[verifier(external_body)]
    pub fn replicas(&self) -> (replicas: Option<i32>)
        ensures
            self@.replicas.is_Some() == replicas.is_Some(),
            replicas.is_Some() ==> replicas.get_Some_0() == self@.replicas.get_Some_0(),
    {
        self.inner.replicas.clone()
    }

    #[verifier(external_body)]
    pub fn selector(&self) -> (selector: LabelSelector)
        ensures selector@ == self@.selector,
    {
        LabelSelector::from_kube(self.inner.selector.clone())
    }

    #[verifier(external_body)]
    pub fn service_name(&self) -> (service_name: String)
        ensures service_name@ == self@.service_name,
    {
        self.inner.service_name.clone()
    }

    #[verifier(external_body)]
    pub fn pod_management_policy(&self) -> (pod_management_policy: Option<String>)
        ensures
            self@.pod_management_policy.is_Some() == pod_management_policy.is_Some(),
            pod_management_policy.is_Some() ==> pod_management_policy.get_Some_0()@ == self@.pod_management_policy.get_Some_0(),
    {
        self.inner.pod_management_policy.clone()
    }

    #[verifier(external_body)]
    pub fn volume_claim_templates(&self) -> (volume_claim_templates: Option<Vec<PersistentVolumeClaim>>)
        ensures
            self@.volume_claim_templates.is_Some() == volume_claim_templates.is_Some(),
            volume_claim_templates.is_Some() ==> volume_claim_templates.get_Some_0()@.map_values(|p: PersistentVolumeClaim| p@) == self@.volume_claim_templates.get_Some_0(),
    {
        match &self.inner.volume_claim_templates {
            Some(p) => Some(p.into_iter().map(|item| PersistentVolumeClaim::from_kube(item.clone())).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn template(&self) -> (template: PodTemplateSpec)
        ensures template@ == self@.template,
    {
        PodTemplateSpec::from_kube(self.inner.template.clone())
    }

    #[verifier(external_body)]
    pub fn persistent_volume_claim_retention_policy(&self) -> (persistent_volume_claim_retention_policy: Option<StatefulSetPersistentVolumeClaimRetentionPolicy>)
        ensures
            self@.persistent_volume_claim_retention_policy.is_Some() == persistent_volume_claim_retention_policy.is_Some(),
            persistent_volume_claim_retention_policy.is_Some() ==> persistent_volume_claim_retention_policy.get_Some_0()@ == self@.persistent_volume_claim_retention_policy.get_Some_0(),
    {
        match &self.inner.persistent_volume_claim_retention_policy {
            Some(p) => Some(StatefulSetPersistentVolumeClaimRetentionPolicy::from_kube(p.clone())),
            None => None,
        }
    }
}

#[verifier(external_body)]
pub struct StatefulSetPersistentVolumeClaimRetentionPolicy {
    inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy,
}

impl StatefulSetPersistentVolumeClaimRetentionPolicy {
    pub uninterp spec fn view(&self) -> StatefulSetPersistentVolumeClaimRetentionPolicyView;

    #[verifier(external_body)]
    pub fn default() -> (pvc_retention_policy: StatefulSetPersistentVolumeClaimRetentionPolicy)
        ensures pvc_retention_policy@ == StatefulSetPersistentVolumeClaimRetentionPolicyView::default(),
    {
        StatefulSetPersistentVolumeClaimRetentionPolicy { inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        StatefulSetPersistentVolumeClaimRetentionPolicy { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_when_deleted(&mut self, when_deleted: String)
        ensures self@ == old(self)@.with_when_deleted(when_deleted@),
    {
        self.inner.when_deleted = Some(when_deleted)
    }

    #[verifier(external_body)]
    pub fn set_when_scaled(&mut self, when_scaled: String)
        ensures self@ == old(self)@.with_when_scaled(when_scaled@),
    {
        self.inner.when_scaled = Some(when_scaled)
    }
}

#[verifier(external_body)]
pub struct StatefulSetStatus {
    inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetStatus,
}

impl StatefulSetStatus {
    pub uninterp spec fn view(&self) -> StatefulSetStatusView;

    #[verifier(external_body)]
    pub fn ready_replicas(&self) -> (ready_replicas: Option<i32>)
        ensures
            self@.ready_replicas.is_Some() == ready_replicas.is_Some(),
            ready_replicas.is_Some() ==> ready_replicas.get_Some_0() == self@.ready_replicas.get_Some_0(),
    {
        self.inner.ready_replicas.clone()
    }
}

}

implement_resource_wrapper_trait!(
    StatefulSet,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSet
);

implement_resource_wrapper_trait!(
    StatefulSetSpec,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec
);

implement_resource_wrapper_trait!(
    StatefulSetStatus,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSetStatus
);

implement_resource_wrapper_trait!(
    StatefulSetPersistentVolumeClaimRetentionPolicy,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy
);
