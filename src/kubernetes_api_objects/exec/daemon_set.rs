// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, label_selector::*, object_meta::*, pod_template_spec::*,
    resource::*,
};
use crate::kubernetes_api_objects::spec::{daemon_set::*, resource::*};
use vstd::prelude::*;

// DaemonSet is a type of API object used for managing daemon applications,
// mainly a group of Pods and PersistentVolumeClaims attached to the Pods.
// A DaemonSet object allows different types of Volumes attached to the pods,
// including ConfigMaps, Secrets and PersistentVolumeClaims.
// It also exposes the applications using a headless service.
//
// This definition is a wrapper of DaemonSet defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/apps/v1/daemon_set.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/concepts/workloads/controllers/daemonset/.

implement_object_wrapper_type!(
    DaemonSet,
    deps_hack::k8s_openapi::api::apps::v1::DaemonSet,
    DaemonSetView
);

implement_field_wrapper_type!(
    DaemonSetSpec,
    deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec,
    DaemonSetSpecView
);

implement_field_wrapper_type!(
    DaemonSetStatus,
    deps_hack::k8s_openapi::api::apps::v1::DaemonSetStatus,
    DaemonSetStatusView
);

verus! {

impl DaemonSet {
    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<DaemonSetSpec>)
        ensures
            self@.spec is Some == spec is Some,
            spec is Some ==> spec->0@ == self@.spec->0,
    {
        if self.inner.spec.is_none() { None } else { Some(DaemonSetSpec::from_kube(self.inner.spec.as_ref().unwrap().clone())) }
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: DaemonSetSpec)
        ensures self@ == old(self)@.with_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }
}

impl DaemonSetSpec {
    #[verifier(external_body)]
    pub fn set_selector(&mut self, selector: LabelSelector)
        ensures self@ == old(self)@.with_selector(selector@),
    {
        self.inner.selector = selector.into_kube()
    }

    #[verifier(external_body)]
    pub fn set_template(&mut self, template: PodTemplateSpec)
        ensures self@ == old(self)@.with_template(template@),
    {
        self.inner.template = template.into_kube()
    }

    #[verifier(external_body)]
    pub fn selector(&self) -> (selector: LabelSelector)
        ensures selector@ == self@.selector,
    {
        LabelSelector::from_kube(self.inner.selector.clone())
    }

    #[verifier(external_body)]
    pub fn template(&self) -> (template: PodTemplateSpec)
        ensures template@ == self@.template,
    {
        PodTemplateSpec::from_kube(self.inner.template.clone())
    }
}

impl DaemonSetStatus {
    #[verifier(external_body)]
    pub fn number_ready(&self) -> (number_ready: i32)
        ensures self@.number_ready == number_ready as int,
    {
        self.inner.number_ready
    }
}

}

implement_resource_wrapper_trait!(DaemonSet, deps_hack::k8s_openapi::api::apps::v1::DaemonSet);

implement_resource_wrapper_trait!(
    DaemonSetSpec,
    deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec
);

implement_resource_wrapper_trait!(
    DaemonSetStatus,
    deps_hack::k8s_openapi::api::apps::v1::DaemonSetStatus
);
