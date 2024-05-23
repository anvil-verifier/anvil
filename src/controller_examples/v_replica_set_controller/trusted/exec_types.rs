// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    affinity::*, api_resource::*, dynamic::*, label_selector::*, object_meta::*,
    owner_reference::*, pod_template_spec::*, resource::*, resource_requirements::*,
    stateful_set::*, toleration::*,
};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::v_replica_set_controller::trusted::{spec_types, step::*};
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

/// VReplicaSetReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct VReplicaSetReconcileState {
    // reconcile_step, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_step: VReplicaSetReconcileStep,
    pub latest_config_map_rv_opt: Option<String>,
}

impl std::clone::Clone for VReplicaSetReconcileState {

    #[verifier(external_body)]
    fn clone(&self) -> (result: VReplicaSetReconcileState)
        ensures result == self
    {
        VReplicaSetReconcileState {
            reconcile_step: self.reconcile_step,
            latest_config_map_rv_opt:
                match &self.latest_config_map_rv_opt {
                    Some(n) => Some(n.clone()),
                    None => None,
                }
        }
    }
}

impl View for VReplicaSetReconcileState {
    type V = spec_types::VReplicaSetReconcileState;

    open spec fn view(&self) -> spec_types::VReplicaSetReconcileState {
        spec_types::VReplicaSetReconcileState {
            reconcile_step: self.reconcile_step,
            latest_config_map_rv_opt:
                match self.latest_config_map_rv_opt {
                    Some(s) => Some(s@),
                    None => None,
                },
        }
    }
}

#[verifier(external_body)]
pub struct VReplicaSet {
    inner: deps_hack::VReplicaSet
}

impl View for VReplicaSet {
    type V = spec_types::VReplicaSetView;

    spec fn view(&self) -> spec_types::VReplicaSetView;
}

impl VReplicaSet {
    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: VReplicaSetSpec)
        ensures spec@ == self@.spec,
    {
        VReplicaSetSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == spec_types::VReplicaSetView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::VReplicaSet>(&()))
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
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<VReplicaSet, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == spec_types::VReplicaSetView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == spec_types::VReplicaSetView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::VReplicaSet>();
        if parse_result.is_ok() {
            let res = VReplicaSet { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::VReplicaSet> for VReplicaSet {
    fn from_kube(inner: deps_hack::VReplicaSet) -> VReplicaSet { VReplicaSet { inner: inner } }

    fn into_kube(self) -> deps_hack::VReplicaSet { self.inner }
}

#[verifier(external_body)]
pub struct VReplicaSetSpec {
    inner: deps_hack::VReplicaSetSpec,
}

impl VReplicaSetSpec {
    pub spec fn view(&self) -> spec_types::VReplicaSetSpecView;

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
}

}
