// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    affinity::*, api_resource::*, container::*, dynamic::*, object_meta::*, resource::*,
    resource_requirements::*, toleration::*, volume::*,
};
use crate::kubernetes_api_objects::spec::{pod::*, resource::*};
use crate::vstd_ext::{string_map::*, string_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

/// Pod is a type of API object used for grouping one or more containers that share storage and network resources.
/// This is the smallest deployable unit in Kubernetes.
///
/// You can specify the Container(s), including the images and commands, and the Volume(s),
/// such as a ConfigMap or a Secret, in the specification of a Pod (i.e., PodSpec).
///
/// This definition is a wrapper of Pod defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/pod.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/workloads/pods/.

#[verifier(external_body)]
pub struct Pod {
    inner: deps_hack::k8s_openapi::api::core::v1::Pod,
}

impl Pod {
    pub spec fn view(&self) -> PodView;

    #[verifier(external_body)]
    pub fn default() -> (pod: Pod)
        ensures pod@ == PodView::default(),
    {
        Pod { inner: deps_hack::k8s_openapi::api::core::v1::Pod::default() }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<PodSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        match &self.inner.spec {
            Some(s) => Some(PodSpec::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: PodSpec)
        ensures self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Pod { self.inner }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Pod) -> (pod: Pod)
    {
        Pod { inner: inner }
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == PodView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::Pod>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
    }

    /// Convert a DynamicObject to a Pod
    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<Pod, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == PodView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == PodView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::Pod>();
        if parse_result.is_ok() {
            let res = Pod { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external_body)]
pub struct PodSpec {
    inner: deps_hack::k8s_openapi::api::core::v1::PodSpec,
}

impl PodSpec {
    pub spec fn view(&self) -> PodSpecView;

    #[verifier(external_body)]
    pub fn default() -> (pod_spec: PodSpec)
        ensures pod_spec@ == PodSpecView::default(),
    {
        PodSpec { inner: deps_hack::k8s_openapi::api::core::v1::PodSpec::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (p: PodSpec)
        ensures p@ == self@,
    {
        PodSpec { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_affinity(&mut self, affinity: Affinity)
        ensures self@ == old(self)@.set_affinity(affinity@),
    {
        self.inner.affinity = Some(affinity.into_kube())
    }

    #[verifier(external_body)]
    pub fn overwrite_affinity(&mut self, affinity: Option<Affinity>)
        ensures
            affinity.is_None() ==> self@ == old(self)@.unset_affinity(),
            affinity.is_Some() ==> self@ == old(self)@.set_affinity(affinity.get_Some_0()@),
    {
        match affinity {
            Some(a) => self.inner.affinity = Some(a.into_kube()),
            None => self.inner.affinity = None,
        }
    }

    #[verifier(external_body)]
    pub fn set_containers(&mut self, containers: Vec<Container>)
        ensures self@ == old(self)@.set_containers(containers@.map_values(|container: Container| container@)),
    {
        self.inner.containers = containers.into_iter().map(|container: Container| container.into_kube()).collect()
    }

    #[verifier(external_body)]
    pub fn set_volumes(&mut self, volumes: Vec<Volume>)
        ensures self@ == old(self)@.set_volumes(volumes@.map_values(|vol: Volume| vol@)),
    {
        self.inner.volumes = Some(volumes.into_iter().map(|vol: Volume| vol.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_init_containers(&mut self, init_containers: Vec<Container>)
        ensures self@ == old(self)@.set_init_containers(init_containers@.map_values(|container: Container| container@)),
    {
        self.inner.init_containers = Some(init_containers.into_iter().map(|container: Container| container.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_service_account_name(&mut self, service_account: String)
        ensures self@ == old(self)@.set_service_account_name(service_account@),
    {
        self.inner.service_account_name = Some(service_account.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn set_tolerations(&mut self, tolerations: Vec<Toleration>)
        ensures self@ == old(self)@.set_tolerations(tolerations@.map_values(|toleration: Toleration| toleration@)),
    {
        self.inner.tolerations = Some(tolerations.into_iter().map(|toleration: Toleration| toleration.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn overwrite_tolerations(&mut self, tolerations: Option<Vec<Toleration>>)
        ensures
            tolerations.is_None() ==> self@ == old(self)@.unset_tolerations(),
            tolerations.is_Some() ==> self@ == old(self)@.set_tolerations(tolerations.get_Some_0()@.map_values(|toleration: Toleration| toleration@)),
    {
        match tolerations {
            Some(t) => self.inner.tolerations = Some(t.into_iter().map(|toleration: Toleration| toleration.into_kube()).collect()),
            None => self.inner.tolerations = None,
        }
    }

    #[verifier(external_body)]
    pub fn set_node_selector(&mut self, node_selector: StringMap)
        ensures self@ == old(self)@.set_node_selector(node_selector@),
    {
        self.inner.node_selector = Some(node_selector.into_rust_map())
    }

    #[verifier(external_body)]
    pub fn overwrite_runtime_class_name(&mut self, runtime_class_name: Option<String>)
        ensures self@ == old(self)@.overwrite_runtime_class_name(opt_string_to_view(&runtime_class_name)),
    {
        match runtime_class_name {
            Some(n) => self.inner.runtime_class_name = Some(n.into_rust_string()),
            None => self.inner.runtime_class_name = None,
        }

    }

    #[verifier(external_body)]
    pub fn overwrite_dns_policy(&mut self, dns_policy: Option<String>)
        ensures self@ == old(self)@.overwrite_dns_policy(opt_string_to_view(&dns_policy)),
    {
        match dns_policy {
            Some(n) => self.inner.dns_policy = Some(n.into_rust_string()),
            None => self.inner.dns_policy = None,
        }

    }

    #[verifier(external_body)]
    pub fn overwrite_scheduler_name(&mut self, scheduler_name: Option<String>)
        ensures self@ == old(self)@.overwrite_scheduler_name(opt_string_to_view(&scheduler_name)),
    {
        match scheduler_name {
            Some(n) => self.inner.scheduler_name = Some(n.into_rust_string()),
            None => self.inner.scheduler_name = None,
        }
    }

    #[verifier(external_body)]
    pub fn overwrite_priority_class_name(&mut self, priority_class_name: Option<String>)
        ensures self@ == old(self)@.overwrite_priority_class_name(opt_string_to_view(&priority_class_name)),
    {
        match priority_class_name {
            Some(n) => self.inner.priority_class_name = Some(n.into_rust_string()),
            None => self.inner.priority_class_name = None,
        }
    }

    #[verifier(external_body)]
    pub fn set_security_context(&mut self, security_context: PodSecurityContext)
        ensures self@ == old(self)@.set_security_context(security_context@),
    {
        self.inner.security_context = Some(security_context.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_host_network(&mut self, host_network: bool)
        ensures self@ == old(self)@.set_host_network(host_network),
    {
        self.inner.host_network = Some(host_network);
    }

    #[verifier(external_body)]
    pub fn set_termination_grace_period_seconds(&mut self, termination_grace_period_seconds: i64)
        ensures self@ == old(self)@.set_termination_grace_period_seconds(termination_grace_period_seconds as int),
    {
        self.inner.termination_grace_period_seconds = Some(termination_grace_period_seconds);
    }

    #[verifier(external_body)]
    pub fn set_image_pull_secrets(&mut self, image_pull_secrets: Vec<LocalObjectReference>)
        ensures self@ == old(self)@.set_image_pull_secrets(image_pull_secrets@.map_values(|r: LocalObjectReference| r@)),
    {
        self.inner.image_pull_secrets = Some(image_pull_secrets.into_iter().map(|r: LocalObjectReference| r.into_kube()).collect())
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::PodSpec) -> PodSpec { PodSpec { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::PodSpec { self.inner }
}

#[verifier(external_body)]
pub struct PodSecurityContext {
    inner: deps_hack::k8s_openapi::api::core::v1::PodSecurityContext,
}

impl View for PodSecurityContext {
    type V = PodSecurityContextView;

    spec fn view(&self) -> PodSecurityContextView;
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::PodSecurityContext> for PodSecurityContext {
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::PodSecurityContext) -> PodSecurityContext { PodSecurityContext { inner: inner } }

    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::PodSecurityContext { self.inner }
}

#[verifier(external_body)]
pub struct LocalObjectReference {
    inner: deps_hack::k8s_openapi::api::core::v1::LocalObjectReference,
}

impl View for LocalObjectReference {
    type V = LocalObjectReferenceView;

    spec fn view(&self) -> LocalObjectReferenceView;
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::LocalObjectReference> for LocalObjectReference {
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::LocalObjectReference) -> LocalObjectReference { LocalObjectReference { inner: inner } }

    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::LocalObjectReference { self.inner }
}

}
