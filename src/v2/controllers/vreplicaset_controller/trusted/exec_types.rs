// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, label_selector::*, pod_template_spec::*, prelude::*,
};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::vreplicaset_controller::trusted::spec_types;
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

implement_resource_wrapper_trait!(VReplicaSet, deps_hack::VReplicaSet);
implement_custom_object_wrapper_type!(
    VReplicaSet,
    deps_hack::VReplicaSet,
    spec_types::VReplicaSetView
);

impl VReplicaSet {

    #[verifier(external_body)]
    pub fn well_formed(&self) -> (b: bool)
        ensures b == self@.well_formed(),
    {
        self.metadata().well_formed()
        && self.metadata().namespace().is_some()
        && self.state_validation()
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: VReplicaSetSpec)
        ensures spec@ == self@.spec,
    {
        VReplicaSetSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: VReplicaSetSpec)
        ensures self@ == old(self)@.with_spec(spec@),
    {
        self.inner.spec = spec.into_kube();
    }

    pub fn state_validation(&self) -> (res: bool)
        ensures
            res == self@.state_validation()
    {

        // replicas doesn't exist (eq to 1) or non-negative
        if let Some(replicas) = self.spec().replicas() {
            if replicas < 0 {
                return false;
            }
        }

        // Check if selector's match_labels exist and are non-empty
        if let Some(match_labels) = self.spec().selector().match_labels() {
            if match_labels.len() <= 0 {
                return false;
            }
        } else {
            return false;
        }

        // template, metadata, and spec exist
        if let Some(template) = self.spec().template() {
            if template.metadata().is_none() || template.spec().is_none() {
                return false;
            }

            if let Some(labels) = template.metadata().unwrap().labels() {
                if !self.spec().selector().matches(labels) {
                    return false;
                }
            } else {
                return false;
            }
        } else {
            return false;
        }

        true
    }
}

implement_resource_wrapper_trait!(VReplicaSetSpec, deps_hack::VReplicaSetSpec);
implement_field_wrapper_type!(
    VReplicaSetSpec,
    deps_hack::VReplicaSetSpec,
    spec_types::VReplicaSetSpecView
);

impl VReplicaSetSpec {

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

    #[verifier(external_body)]
    pub fn set_replicas(&mut self, replicas: i32)
        ensures self@ == old(self)@.with_replicas(replicas as int),
    {
        self.inner.replicas = Some(replicas);
    }

    #[verifier(external_body)]
    pub fn set_selector(&mut self, selector: LabelSelector)
       ensures self@ == old(self)@.with_selector(selector@),
    {
        self.inner.selector = selector.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_template(&mut self, template: PodTemplateSpec)
        ensures self@ == old(self)@.with_template(template@),
    {
        self.inner.template = Some(template.into_kube());
    }
}

}