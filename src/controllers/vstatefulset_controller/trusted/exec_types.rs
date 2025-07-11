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
use crate::vstd_ext::string_map::*;
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

// helper function to circumvent the lack of support for String in spec
#[verifier(external_body)]
pub fn string_equal(s1: &String, s2: &str) -> (res: bool)
    ensures
        s1@ == s2@ <==> res,
{
    s1 == s2
}

// since this uses kubernetes_cluster, we cannot import kubernetes_cluster/common.rs
// TODO: update state_validation specs for PersistentVolumeClaim
impl PersistentVolumeClaim {
    pub fn state_validation(&self) -> (res: bool)
        ensures
            res == self@.state_validation()
    {
        self.spec().is_some()
    }
}

#[verifier(external_body)]
pub struct VStatefulSet {
    inner: deps_hack::VStatefulSet
}

impl View for VStatefulSet {
    type V = spec_types::VStatefulSetView;

    uninterp spec fn view(&self) -> spec_types::VStatefulSetView;
}

impl VStatefulSet {
    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: VStatefulSetSpec)
        ensures spec@ == self@.spec,
    {
        VStatefulSetSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == spec_types::VStatefulSetView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::VStatefulSet>(&()))
    }

    #[verifier(external_body)]
    pub fn controller_owner_ref(&self) -> (owner_reference: OwnerReference)
        ensures owner_reference@ == self@.controller_owner_ref(),
    {
        // We can safely unwrap here because the trait method implementation always returns a Some(...)
        OwnerReference::from_kube(self.inner.controller_owner_ref(&()).unwrap())
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<VStatefulSet, UnmarshalError>)
        ensures
            res is Ok == spec_types::VStatefulSetView::unmarshal(obj@) is Ok,
            res is Ok ==> res->Ok_0@ == spec_types::VStatefulSetView::unmarshal(obj@)->Ok_0,
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::VStatefulSet>();
        if parse_result.is_ok() {
            let res = VStatefulSet { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(())
        }
    }

    pub fn state_validation(&self) -> (res: bool)
        ensures
            res == self@.state_validation()
    {
        // replicas
        if let Some(replicas) = self.spec().replicas() {
            // non-negative
            if replicas < 0 {
                return false;
            }
        }

        // updateStrategy
        if let Some(update_strategy) = self.spec().update_strategy() {
            if let Some(update_strategy_type) = update_strategy.type_() {
                // update_strategy is either "Recreate" or "RollingUpdate"
                if string_equal(&update_strategy_type, "RollingUpdate") {
                    if let Some(rolling_update) = update_strategy.rolling_update() {
                        if let Some(partition) = rolling_update.partition() {
                            // partition should be non-negative
                            if partition < 0 {
                                return false;
                            }
                        }
                        if let Some(max_unavailable) = rolling_update.max_unavailable() {
                            // max_unavailable should be positive
                            if max_unavailable <= 0 {
                                return false;
                            }
                        }
                    }
                }
                else if string_equal(&update_strategy_type, "OnDelete") {
                    // RollingUpdate block should not exist
                    if update_strategy.rolling_update().is_some() {
                        return false;
                    }
                }
                else {
                    return false;
                }
            }
        }

        // podManagementPolicy
        if let Some(pod_management_policy) = self.spec().pod_management_policy() {
            // should be either "OrderedReady" or "Parallel"
            if !string_equal(&pod_management_policy, "OrderedReady") && !string_equal(&pod_management_policy, "Parallel") {
                return false;
            }
        }

        // volumeClaimTemplates
        if let Some(vct) = self.spec().volume_claim_templates() {
            let mut idx: usize = 0;
            let ghost mut vct_view: Seq<PersistentVolumeClaimView> = Seq::new(vct.len() as nat,|i: int| vct[i]@);
            assert(vct@.map_values(|pvc: PersistentVolumeClaim| pvc@) == vct_view);
            for idx in 0..vct.len()
                invariant
                    0 <= idx <= vct.len(),
                    forall |i: int| 0 <= i < idx ==> #[trigger] vct[i]@.state_validation(),
                    vct@.map_values(|pvc: PersistentVolumeClaim| pvc@) == vct_view,
                    self@.spec.volume_claim_templates is Some,
                    vct_view == self@.spec.volume_claim_templates->0,
            {
                let pvc_sv = vct[idx].state_validation();
                assert(pvc_sv == vct_view[idx as int].state_validation());
                if !pvc_sv {
                    return false;
                }
            }
        }

        // minReadySeconds
        if let Some(min_ready_seconds) = self.spec().min_ready_seconds() {
            // cannot be negative
            if min_ready_seconds < 0 {
                return false;
            }
        }

        // persistentVolumeClaimRetentionPolicy
        if let Some(persistent_volume_claim_retention_policy) = self.spec().persistent_volume_claim_retention_policy() {
            // when_deleted and when_scaled should be either "Retain" or "Delete"
            if let Some(when_deleted) = persistent_volume_claim_retention_policy.when_deleted() {
                if !string_equal(&when_deleted, "Retain") && !string_equal(&when_deleted, "Delete") {
                    return false;
                }
            }
            if let Some(when_scaled) = persistent_volume_claim_retention_policy.when_scaled() {
                if !string_equal(&when_scaled, "Retain") && !string_equal(&when_scaled, "Delete") {
                    return false;
                }
            }
        }

        // ordinals
        if let Some(ordinals) = self.spec().ordinals() {
            // start should be non-negative
            if let Some(start) = ordinals.start() {
                if start < 0 {
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

        // template, metadata, and spec exist
        if self.spec().template().metadata().is_none() || self.spec().template().spec().is_none() {
            return false;
        }
        // Map::empty() did not compile
        if !self.spec().selector().matches(self.spec().template().metadata().unwrap().labels().unwrap_or(StringMap::empty())) {
            return false;
        }

        true
    }
}

#[verifier(external_body)]
pub struct VStatefulSetSpec {
    inner: deps_hack::VStatefulSetSpec,
}

impl VStatefulSetSpec {
    pub uninterp spec fn view(&self) -> spec_types::VStatefulSetSpecView;

    #[verifier(external_body)]
    pub fn service_name(&self) -> (service_name: String)
        ensures service_name@ == self@.service_name,
    {
        self.inner.service_name.clone()
    }

    #[verifier(external_body)]
    pub fn replicas(&self) -> (replicas: Option<i32>)
        ensures
            replicas is Some == self@.replicas is Some,
            replicas is Some ==> replicas->0 as int == self@.replicas->0,
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
            template@ == self@.template
    {
        PodTemplateSpec::from_kube(self.inner.template.clone())
    }

    #[verifier(external_body)]
    pub fn update_strategy(&self) -> (update_strategy: Option<StatefulSetUpdateStrategy>)
        ensures
            update_strategy is Some == self@.update_strategy is Some,
            update_strategy is Some ==> update_strategy->0@ == self@.update_strategy->0,
    {
        match &self.inner.update_strategy {
            Some(us) => Some(StatefulSetUpdateStrategy::from_kube(us.clone())),
            None => None
        }
    }

    #[verifier(external_body)]
    pub fn pod_management_policy(&self) -> (pod_management_policy: Option<String>)
        ensures
            pod_management_policy is Some == self@.pod_management_policy is Some,
            pod_management_policy is Some ==> pod_management_policy->0@ == self@.pod_management_policy->0,
    {
        self.inner.pod_management_policy.clone()
    }

    #[verifier(external_body)]
    pub fn volume_claim_templates(&self) -> (volume_claim_templates: Option<Vec<PersistentVolumeClaim>>)
        ensures
            volume_claim_templates is Some == self@.volume_claim_templates is Some,
            volume_claim_templates is Some ==> volume_claim_templates->0@.map_values(|pvc: PersistentVolumeClaim| pvc@) == self@.volume_claim_templates->0
    {
        match &self.inner.volume_claim_templates {
            Some(vct) => Some(vct.iter().map(|v| PersistentVolumeClaim::from_kube(v.clone())).collect()),
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
    pub fn persistent_volume_claim_retention_policy(&self) -> (retention_policy: Option<StatefulSetPersistentVolumeClaimRetentionPolicy>)
        ensures
            retention_policy is Some == self@.persistent_volume_claim_retention_policy is Some,
            retention_policy is Some ==> retention_policy->0@ == self@.persistent_volume_claim_retention_policy->0,
    {
        match &self.inner.persistent_volume_claim_retention_policy {
            Some(pvcrp) => Some(StatefulSetPersistentVolumeClaimRetentionPolicy::from_kube(pvcrp.clone())),
            None => None
        }
    }

    #[verifier(external_body)]
    pub fn ordinals(&self) -> (ordinals: Option<StatefulSetOrdinals>)
        ensures
            ordinals is Some == self@.ordinals is Some,
            ordinals is Some ==> ordinals->0@ == self@.ordinals->0,
    {
        match &self.inner.ordinals {
            Some(o) => Some(StatefulSetOrdinals::from_kube(o.clone())),
            None => None
        }
    }
}

// TODO: merge the definitions below into kubernetes_api_objects

#[verifier(external_body)]
pub struct StatefulSetUpdateStrategy {
    inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetUpdateStrategy,
}

impl StatefulSetUpdateStrategy {
    pub uninterp spec fn view(&self) -> spec_types::StatefulSetUpdateStrategyView;

    #[verifier(external_body)]
    pub fn default() -> (strategy: StatefulSetUpdateStrategy)
        ensures strategy@ == spec_types::StatefulSetUpdateStrategyView::default(),
    {
        StatefulSetUpdateStrategy {
            inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetUpdateStrategy::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (strategy: StatefulSetUpdateStrategy)
        ensures strategy@ == self@,
    {
        StatefulSetUpdateStrategy { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn type_(&self) -> (type_: Option<String>)
        ensures
            self@.type_ is Some == type_ is Some,
            type_ is Some ==> type_->0@ == self@.type_->0,
    {
        self.inner.type_.clone()
    }

    #[verifier(external_body)]
    pub fn rolling_update(&self) -> (rolling_update: Option<RollingUpdateStatefulSetStrategy>)
        ensures
            self@.rolling_update is Some == rolling_update is Some,
            rolling_update is Some ==> rolling_update->0@ == self@.rolling_update->0,
    {
        match &self.inner.rolling_update {
            Some(ru) => Some(RollingUpdateStatefulSetStrategy::from_kube(ru.clone())),
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
    pub fn set_rolling_update(&mut self, rolling_update: RollingUpdateStatefulSetStrategy)
        ensures self@ == old(self)@.with_rolling_update(rolling_update@),
    {
        self.inner.rolling_update = Some(rolling_update.into_kube());
    }
}

#[verifier(external_body)]
pub struct RollingUpdateStatefulSetStrategy {
    inner: deps_hack::k8s_openapi::api::apps::v1::RollingUpdateStatefulSetStrategy,
}

impl RollingUpdateStatefulSetStrategy {
    pub uninterp spec fn view(&self) -> spec_types::RollingUpdateStatefulSetStrategyView;

    #[verifier(external_body)]
    pub fn default() -> (rolling_update: RollingUpdateStatefulSetStrategy)
        ensures rolling_update@ == spec_types::RollingUpdateStatefulSetStrategyView::default(),
    {
        RollingUpdateStatefulSetStrategy {
            inner: deps_hack::k8s_openapi::api::apps::v1::RollingUpdateStatefulSetStrategy::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (rolling_update: RollingUpdateStatefulSetStrategy)
        ensures rolling_update@ == self@,
    {
        RollingUpdateStatefulSetStrategy { inner: self.inner.clone() }
    }

    // Simplified implementation treating IntOrString values as integers only
    #[verifier(external_body)]
    pub fn partition(&self) -> (partition: Option<i32>)
        ensures
            self@.partition is Some == partition is Some,
            partition is Some ==> partition->0 as int == self@.partition->0,
    {
        self.inner.partition
    }

    #[verifier(external_body)]
    pub fn max_unavailable(&self) -> (max_unavailable: Option<i32>)
        ensures
            self@.max_unavailable is Some == max_unavailable is Some,
            max_unavailable is Some ==> max_unavailable->0 as int == self@.max_unavailable->0,
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
    pub fn set_partition(&mut self, partition: i32)
        ensures self@ == old(self)@.with_partition(partition as int),
    {
        self.inner.partition = Some(partition);
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


#[verifier(external_body)]
pub struct StatefulSetPersistentVolumeClaimRetentionPolicy {
    inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy,
}

impl StatefulSetPersistentVolumeClaimRetentionPolicy {
    pub uninterp spec fn view(&self) -> spec_types::StatefulSetPersistentVolumeClaimRetentionPolicyView;

    #[verifier(external_body)]
    pub fn default() -> (policy: StatefulSetPersistentVolumeClaimRetentionPolicy)
        ensures policy@ == spec_types::StatefulSetPersistentVolumeClaimRetentionPolicyView::default(),
    {
        StatefulSetPersistentVolumeClaimRetentionPolicy {
            inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (policy: StatefulSetPersistentVolumeClaimRetentionPolicy)
        ensures policy@ == self@,
    {
        StatefulSetPersistentVolumeClaimRetentionPolicy { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn when_deleted(&self) -> (when_deleted: Option<String>)
        ensures
            self@.when_deleted is Some == when_deleted is Some,
            when_deleted is Some ==> when_deleted->0@ == self@.when_deleted->0,
    {
        self.inner.when_deleted.clone()
    }

    #[verifier(external_body)]
    pub fn when_scaled(&self) -> (when_scaled: Option<String>)
        ensures
            self@.when_scaled is Some == when_scaled is Some,
            when_scaled is Some ==> when_scaled->0@ == self@.when_scaled->0,
    {
        self.inner.when_scaled.clone()
    }

    #[verifier(external_body)]
    pub fn set_when_deleted(&mut self, when_deleted: String)
        ensures self@ == old(self)@.with_when_deleted(when_deleted@),
    {
        self.inner.when_deleted = Some(when_deleted);
    }

    #[verifier(external_body)]
    pub fn set_when_scaled(&mut self, when_scaled: String)
        ensures self@ == old(self)@.with_when_scaled(when_scaled@),
    {
        self.inner.when_scaled = Some(when_scaled);
    }
}

#[verifier(external_body)]
pub struct StatefulSetOrdinals {
    inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetOrdinals,
}

impl StatefulSetOrdinals {
    pub uninterp spec fn view(&self) -> spec_types::StatefulSetOrdinalsView;

    #[verifier(external_body)]
    pub fn default() -> (ordinals: StatefulSetOrdinals)
        ensures ordinals@ == spec_types::StatefulSetOrdinalsView::default(),
    {
        StatefulSetOrdinals {
            inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetOrdinals::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (ordinals: StatefulSetOrdinals)
        ensures ordinals@ == self@,
    {
        StatefulSetOrdinals { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn start(&self) -> (start: Option<i32>)
        ensures
            self@.start is Some == start is Some,
            start is Some ==> start->0 as int == self@.start->0,
    {
        match &self.inner.start {
            Some(s) => Some(*s),
            None => None
        }
    }

    #[verifier(external_body)]
    pub fn set_start(&mut self, start: i32)
        ensures self@ == old(self)@.with_start(start as int),
    {
        self.inner.start = Some(start);
    }
}

}

implement_resource_wrapper_trait!(VStatefulSet, deps_hack::VStatefulSet);

implement_resource_wrapper_trait!(
    StatefulSetUpdateStrategy,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSetUpdateStrategy
);

implement_resource_wrapper_trait!(
    RollingUpdateStatefulSetStrategy,
    deps_hack::k8s_openapi::api::apps::v1::RollingUpdateStatefulSetStrategy
);

implement_resource_wrapper_trait!(
    StatefulSetOrdinals,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSetOrdinals
);

implement_resource_wrapper_trait!(
    StatefulSetPersistentVolumeClaimRetentionPolicy,
    deps_hack::k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy
);
