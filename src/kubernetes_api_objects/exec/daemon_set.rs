// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, label_selector::*, object_meta::*, pod_template_spec::*,
    resource::*,
};
use crate::kubernetes_api_objects::spec::{daemon_set::*, resource::*};
use crate::vstd_ext::{string_map::*, string_view::*};
use vstd::{prelude::*, seq_lib::*, string::*};

verus! {

/// DaemonSet is a type of API object used for managing daemon applications,
/// mainly a group of Pods and PersistentVolumeClaims attached to the Pods.
/// A DaemonSet object allows different types of Volumes attached to the pods,
/// including ConfigMaps, Secrets and PersistentVolumeClaims.
/// It also exposes the applications using a headless service.
///
/// This definition is a wrapper of DaemonSet defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/apps/v1/daemon_set.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/workloads/controllers/daemonset/.

#[verifier(external_body)]
pub struct DaemonSet {
    inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSet,
}

impl DaemonSet {
    pub spec fn view(&self) -> DaemonSetView;

    #[verifier(external_body)]
    pub fn default() -> (daemon_set: DaemonSet)
        ensures daemon_set@ == DaemonSetView::default(),
    {
        DaemonSet { inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSet::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        DaemonSet { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<DaemonSetSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        if self.inner.spec.is_none() { None } else { Some(DaemonSetSpec::from_kube(self.inner.spec.as_ref().unwrap().clone())) }
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: DaemonSetSpec)
        ensures self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == DaemonSetView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::apps::v1::DaemonSet>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
    }

    /// Convert a DynamicObject to a DaemonSet
    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<DaemonSet, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == DaemonSetView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == DaemonSetView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::apps::v1::DaemonSet>();
        if parse_result.is_ok() {
            let res = DaemonSet { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::api::apps::v1::DaemonSet> for DaemonSet {
    fn from_kube(inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSet) -> DaemonSet { DaemonSet { inner: inner } }

    fn into_kube(self) -> deps_hack::k8s_openapi::api::apps::v1::DaemonSet { self.inner }
}

#[verifier(external_body)]
pub struct DaemonSetSpec {
    inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec,
}

impl DaemonSetSpec {
    pub spec fn view(&self) -> DaemonSetSpecView;

    #[verifier(external_body)]
    pub fn default() -> (daemon_set_spec: DaemonSetSpec)
        ensures daemon_set_spec@ == DaemonSetSpecView::default(),
    {
        DaemonSetSpec { inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        DaemonSetSpec { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_selector(&mut self, selector: LabelSelector)
        ensures self@ == old(self)@.set_selector(selector@),
    {
        self.inner.selector = selector.into_kube()
    }

    #[verifier(external_body)]
    pub fn set_template(&mut self, template: PodTemplateSpec)
        ensures self@ == old(self)@.set_template(template@),
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

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec> for DaemonSetSpec {
    fn from_kube(inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec) -> DaemonSetSpec { DaemonSetSpec { inner: inner } }

    fn into_kube(self) -> deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec { self.inner }
}

#[verifier(external_body)]
pub struct DaemonSetStatus {
    inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSetStatus,
}

impl DaemonSetStatus {
    pub spec fn view(&self) -> DaemonSetStatusView;

    #[verifier(external_body)]
    pub fn number_ready(&self) -> (number_ready: i32)
        ensures self@.number_ready == number_ready as int,
    {
        self.inner.number_ready
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::api::apps::v1::DaemonSetStatus> for DaemonSetStatus {
    fn from_kube(inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSetStatus) -> DaemonSetStatus { DaemonSetStatus { inner: inner } }

    fn into_kube(self) -> deps_hack::k8s_openapi::api::apps::v1::DaemonSetStatus { self.inner }
}

}
