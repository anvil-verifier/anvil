// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, label_selector::*, pod_template_spec::*, prelude::*, resource::*,
};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::vdeployment_controller::trusted::spec_types;
use crate::vstd_ext::string_view::*;
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

implement_custom_object_wrapper_type!(
    VDeployment,
    deps_hack::VDeployment,
    spec_types::VDeploymentView
);

implement_resource_wrapper_trait!(
    VDeployment,
    deps_hack::VDeployment
);

impl VDeployment {
    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: VDeploymentSpec)
        ensures spec@ == self@.spec,
    {
        VDeploymentSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external_body)]
    pub fn well_formed(&self) -> (b: bool)
        ensures b == self@.well_formed(),
    {
        self.metadata().well_formed()
        && self.metadata().namespace().is_some()
        && self.state_validation()
    }

    // similar to VReplicaSet::state_validation
    pub fn state_validation(&self) -> (res: bool)
        ensures
            res == self@.state_validation(),
    {
        
        // replicas doesn't exist (eq to 1) or non-negative
        if let Some(replicas) = self.spec().replicas() {
            if replicas < 0 {
                return false;
            }
        }

        match (self.spec().min_ready_seconds(), self.spec().progress_deadline_seconds()) {
            // minReadySeconds cannot be negative and must be less than progressDeadlineSeconds
            (Some(min_ready_seconds), Some(progress_deadline_seconds)) => {
                if min_ready_seconds >= progress_deadline_seconds || min_ready_seconds < 0 {
                    return false;
                }
            },
            // minReadySeconds should be smaller than the default value of progressDeadlineSeconds 600
            (Some(min_ready_seconds), None) => {
                if min_ready_seconds >= 600 || min_ready_seconds < 0 {
                    return false;
                }
            },
            // progressDeadlineSeconds should be greater than the default value of minReadySeconds 0
            (None, Some(progress_deadline_seconds)) => {
                if progress_deadline_seconds <= 0 {
                    return false;
                }
            },
            (None, None) => {}
        }

        if let Some(strategy) = self.spec().strategy() {
            if let Some(strategy_type) = strategy.type_() {
                // strategy is either "Recreate" or "RollingUpdate"
                if string_equal(&strategy_type, "RollingUpdate") {
                    if let Some(rolling_update) = strategy.rolling_update() {
                        // maxSurge and maxUnavailable cannot be negative
                        match (rolling_update.max_surge(), rolling_update.max_unavailable()) {
                            (Some(max_surge), Some(max_unavailable)) => {
                                // cannot both be 0
                                if max_surge < 0 || max_unavailable < 0 || (max_surge == 0 && max_unavailable == 0) {
                                    return false;
                                }
                            },
                            (Some(max_surge), None) => {
                                if max_surge < 0 {
                                    return false;
                                }
                            },
                            (None, Some(max_unavailable)) => {
                                if max_unavailable < 0 {
                                    return false;
                                }
                            },
                            (None, None) => {}
                        }
                    }
                }
                else if string_equal(&strategy_type, "Recreate") {
                    // RollingUpdate block should not exist
                    if strategy.rolling_update().is_some() {
                        return false;
                    }
                }
                else {
                    return false;
                }
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

        // template metadata and spec exist
        let template = self.spec().template();
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

        true

    }
}

implement_view_trait!(
    VDeploymentSpec,
    spec_types::VDeploymentSpecView
);

#[verifier(external_body)]
pub struct VDeploymentSpec {
    inner: deps_hack::VDeploymentSpec,
}

impl VDeploymentSpec {

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
    pub fn template(&self) -> (template: PodTemplateSpec)
        ensures
            template@ == self@.template,
    {
        PodTemplateSpec::from_kube(self.inner.template.clone())
    }

    #[verifier(external_body)]
    pub fn min_ready_seconds(&self) -> (min_ready_seconds: Option<i32>)
        ensures
            min_ready_seconds.is_Some() == self@.min_ready_seconds.is_Some(),
            min_ready_seconds.is_Some() ==> min_ready_seconds.get_Some_0() as int == self@.min_ready_seconds.get_Some_0(),
    {
        self.inner.min_ready_seconds
    }

    #[verifier(external_body)]
    pub fn progress_deadline_seconds(&self) -> (progress_deadline: Option<i32>)
        ensures
            progress_deadline.is_Some() == self@.progress_deadline_seconds.is_Some(),
            progress_deadline.is_Some() ==> progress_deadline.get_Some_0() as int == self@.progress_deadline_seconds.get_Some_0(),
    {
        self.inner.progress_deadline_seconds
    }

    #[verifier(external_body)]
    pub fn strategy(&self) -> (strategy: Option<DeploymentStrategy>)
        ensures
            strategy.is_Some() == self@.strategy.is_Some(),
            strategy.is_Some() ==> strategy.get_Some_0()@ == self@.strategy.get_Some_0(),
    {
        match &self.inner.strategy {
            Some(s) => Some(DeploymentStrategy::from_kube(s.clone())),
            None => None
        }
    }

    #[verifier(external_body)]
    pub fn paused(&self) -> (paused: Option<bool>)
        ensures
            paused.is_Some() == self@.paused.is_Some(),
            paused.is_Some() ==> paused.get_Some_0() == self@.paused.get_Some_0(),
    {
        self.inner.paused
    }
}

implement_field_wrapper_type!(
    DeploymentStrategy,
    deps_hack::k8s_openapi::api::apps::v1::DeploymentStrategy,
    spec_types::DeploymentStrategyView
);

implement_resource_wrapper_trait!(
    DeploymentStrategy,
    deps_hack::k8s_openapi::api::apps::v1::DeploymentStrategy
);


impl DeploymentStrategy {

    #[verifier(external_body)]
    pub fn type_(&self) -> (type_: Option<String>)
        ensures
            self@.type_.is_Some() == type_.is_Some(),
            type_.is_Some() ==> type_.get_Some_0()@ == self@.type_.get_Some_0(),
    {
        self.inner.type_.clone()
    }

    #[verifier(external_body)]
    pub fn rolling_update(&self) -> (rolling_update: Option<RollingUpdateDeployment>)
        ensures
            self@.rolling_update.is_Some() == rolling_update.is_Some(),
            rolling_update.is_Some() ==> rolling_update.get_Some_0()@ == self@.rolling_update.get_Some_0(),
    {
        match &self.inner.rolling_update {
            Some(ru) => Some(RollingUpdateDeployment::from_kube(ru.clone())),
            None => None
        }
    }

    #[verifier(external_body)]
    pub fn set_type(&mut self, type_: String)
        ensures self@ == old(self)@.with_type(type_@),
    {
        self.inner.type_ = Some(type_);
    }

    #[verifier(external_body)]
    pub fn set_rolling_update(&mut self, rolling_update: RollingUpdateDeployment)
        ensures self@ == old(self)@.with_rolling_update(rolling_update@),
    {
        self.inner.rolling_update = Some(rolling_update.into_kube());
    }
}

implement_field_wrapper_type!(
    RollingUpdateDeployment,
    deps_hack::k8s_openapi::api::apps::v1::RollingUpdateDeployment,
    spec_types::RollingUpdateDeploymentView
);

implement_resource_wrapper_trait!(
    RollingUpdateDeployment,
    deps_hack::k8s_openapi::api::apps::v1::RollingUpdateDeployment
);

impl RollingUpdateDeployment {
    // Simplified implementation treating IntOrString values as integers only
    #[verifier(external_body)]
    pub fn max_surge(&self) -> (max_surge: Option<i32>)
        ensures
            self@.max_surge.is_Some() == max_surge.is_Some(),
            max_surge.is_Some() ==> max_surge.get_Some_0() as int == self@.max_surge.get_Some_0(),
    {
        match &self.inner.max_surge {
            Some(ms) => match ms {
                deps_hack::k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(i) => Some(*i),
                // Simplification: treat string values as 1 (integer)
                _ => Some(1),
            },
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn max_unavailable(&self) -> (max_unavailable: Option<i32>)
        ensures
            self@.max_unavailable.is_Some() == max_unavailable.is_Some(),
            max_unavailable.is_Some() ==> max_unavailable.get_Some_0() as int == self@.max_unavailable.get_Some_0(),
    {
        match &self.inner.max_unavailable {
            Some(mu) => match mu {
                deps_hack::k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(i) => Some(*i),
                // Simplification: treat string values as 1 (integer)
                _ => Some(1),
            },
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_max_surge(&mut self, max_surge: i32)
        ensures self@ == old(self)@.with_max_surge(max_surge as int),
    {
        self.inner.max_surge = Some(
            deps_hack::k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(max_surge)
        );
    }

    #[verifier(external_body)]
    pub fn set_max_unavailable(&mut self, max_unavailable: i32)
        ensures self@ == old(self)@.with_max_unavailable(max_unavailable as int),
    {
        self.inner.max_unavailable = Some(
            deps_hack::k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(max_unavailable)
        );
    }
}
// END DEPLOYMENT STRATEGY EXEC IMPLEMENTATION
}
