// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, label_selector::*, persistent_volume_claim::*, pod_template_spec::*,
    prelude::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{
    persistent_volume_claim::*, resource::*, volume_resource_requirements::*,
};
use crate::vstatefulset_controller::trusted::spec_types;
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

// We use VStatefulSet to trigger our verified StatefulSet controller
// VStatefulSet coexists with StatefulSet which can be used by other controllers

implement_object_wrapper_type!(
    VStatefulSet,
    deps_hack::VStatefulSet,
    spec_types::VStatefulSetView
);

pub const StatefulSetPodNameLabel: &'static str = "statefulset.kubernetes.io/pod-name";
pub const StatefulSetOrdinalLabel: &'static str = "apps.kubernetes.io/pod-index";

impl VStatefulSet {
    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: VStatefulSetSpec)
        ensures spec@ == self@.spec,
    {
        VStatefulSetSpec::from_kube(self.inner.spec.to_native())
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

implement_field_wrapper_type!(
    VStatefulSetSpec,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec,
    spec_types::VStatefulSetSpecView
);

impl VStatefulSetSpec {
    #[verifier(external_body)]
    pub fn ordinals(&self) -> (ordinals: Option<StatefulSetOrdinals>)
        ensures self@.ordinals == ordinals.deep_view()
    {
        match &self.inner.ordinals {
            Some(o) => Some(StatefulSetOrdinals::from_kube(o.clone())),
            None => None
        }
    }

    #[verifier(external_body)]
    pub fn update_strategy(&self) -> (update_strategy: Option<StatefulSetUpdateStrategy>)
        ensures self@.update_strategy == update_strategy.deep_view()
    {
        match &self.inner.update_strategy {
            Some(us) => Some(StatefulSetUpdateStrategy::from_kube(us.clone())),
            None => None
        }
    }

    #[verifier(external_body)]
    pub fn min_ready_seconds(&self) -> (min_ready_seconds: Option<i32>)
        ensures
            min_ready_seconds is Some == self@.min_ready_seconds is Some,
            min_ready_seconds is Some ==> min_ready_seconds->0 as int == self@.min_ready_seconds->0,
    {
        self.inner.min_ready_seconds
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
        ensures self@.selector == selector@,
    {
        LabelSelector::from_kube(self.inner.selector.clone())
    }

    #[verifier(external_body)]
    pub fn service_name(&self) -> (service_name: String)
        ensures self@.service_name == service_name@,
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
}

// Other internal fields are defined in kubernetes_api_objects::exec::stateful_set

}
