// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, label_selector::*, object_meta::*, persistent_volume_claim::*,
    pod_template_spec::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{resource::*, stateful_set::*};
use vstd::prelude::*;

verus! {

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

implement_field_wrapper_type!(
    StatefulSetSpec,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec,
    StatefulSetSpecView
);

implement_field_wrapper_type!(
    StatefulSetStatus,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSetStatus,
    StatefulSetStatusView
);

implement_field_wrapper_type!(
    StatefulSetPersistentVolumeClaimRetentionPolicy,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy,
    StatefulSetPersistentVolumeClaimRetentionPolicyView
);

impl StatefulSet {
    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<StatefulSetSpec>)
        ensures self@.spec == spec.deep_view()
    {
        if self.inner.spec.is_none() {
            None
        } else {
            Some(StatefulSetSpec::from_kube(self.inner.spec.as_ref().unwrap().clone()))
        }
    }

    #[verifier(external_body)]
    pub fn status(&self) -> (status: Option<StatefulSetStatus>)
        ensures self@.status == status.deep_view()
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

impl StatefulSetSpec {
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
        ensures self@ == old(self)@.with_volume_claim_templates(volume_claim_templates.deep_view()),
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
            self@.replicas is Some == replicas is Some,
            replicas is Some ==> replicas->0 == self@.replicas->0,
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
        ensures self@.pod_management_policy == pod_management_policy.deep_view()
    {
        self.inner.pod_management_policy.clone()
    }

    #[verifier(external_body)]
    pub fn volume_claim_templates(&self) -> (volume_claim_templates: Option<Vec<PersistentVolumeClaim>>)
        ensures self@.volume_claim_templates == volume_claim_templates.deep_view()
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
        ensures self@.persistent_volume_claim_retention_policy == persistent_volume_claim_retention_policy.deep_view()
    {
        match &self.inner.persistent_volume_claim_retention_policy {
            Some(p) => Some(StatefulSetPersistentVolumeClaimRetentionPolicy::from_kube(p.clone())),
            None => None,
        }
    }
}

impl StatefulSetPersistentVolumeClaimRetentionPolicy {
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

impl StatefulSetStatus {
    #[verifier(external_body)]
    pub fn ready_replicas(&self) -> (ready_replicas: Option<i32>)
        ensures
            self@.ready_replicas is Some == ready_replicas is Some,
            ready_replicas is Some ==> ready_replicas->0 == self@.ready_replicas->0,
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
