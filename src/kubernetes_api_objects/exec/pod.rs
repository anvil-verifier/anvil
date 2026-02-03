// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    affinity::*, api_resource::*, container::*, dynamic::*, object_meta::*, resource::*,
    toleration::*, volume::*,
};
use crate::kubernetes_api_objects::spec::{pod::*, resource::*};
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use deps_hack::tracing::{error, info, warn};

verus! {

// Pod is a type of API object used for grouping one or more containers that share storage and network resources.
// This is the smallest deployable unit in Kubernetes.
//
// You can specify the Container(s), including the images and commands, and the Volume(s),
// such as a ConfigMap or a Secret, in the specification of a Pod (i.e., PodSpec).
//
// This definition is a wrapper of Pod defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/pod.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/concepts/workloads/pods/.

implement_object_wrapper_type!(Pod, deps_hack::k8s_openapi::api::core::v1::Pod, PodView);

implement_field_wrapper_type!(
    PodSpec,
    deps_hack::k8s_openapi::api::core::v1::PodSpec,
    PodSpecView
);

implement_field_wrapper_type!(
    PodSecurityContext,
    deps_hack::k8s_openapi::api::core::v1::PodSecurityContext,
    PodSecurityContextView
);

implement_field_wrapper_type!(
    LocalObjectReference,
    deps_hack::k8s_openapi::api::core::v1::LocalObjectReference,
    LocalObjectReferenceView
);

impl Pod {
    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<PodSpec>)
        ensures self@.spec == spec.deep_view(),
    {
        match &self.inner.spec {
            Some(s) => Some(PodSpec::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: PodSpec)
        ensures self@ == old(self)@.with_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }
}

impl PodSpec {
    #[verifier(external_body)]
    pub fn set_affinity(&mut self, affinity: Affinity)
        ensures self@ == old(self)@.with_affinity(affinity@),
    {
        self.inner.affinity = Some(affinity.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_containers(&mut self, containers: Vec<Container>)
        ensures self@ == old(self)@.with_containers(containers.deep_view()),
    {
        self.inner.containers = containers.into_iter().map(|container: Container| container.into_kube()).collect()
    }

    #[verifier(external_body)]
    pub fn volumes(&self) -> (volumes: Option<Vec<Volume>>) 
        ensures volumes.deep_view() == self@.volumes
    {
        match &self.inner.volumes {
            Some(vols) => {
                Some(vols.into_iter().map(|v| Volume::from_kube(v.clone())).collect())
            }
            None => None
        }
    }

    #[verifier(external_body)]
    pub fn set_volumes(&mut self, volumes: Vec<Volume>)
        ensures self@ == old(self)@.with_volumes(volumes.deep_view()),
    {
        self.inner.volumes = Some(volumes.into_iter().map(|vol: Volume| vol.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn unset_volumes(&mut self)
        ensures self@ == old(self)@.without_volumes(),
    {
        self.inner.volumes = None;
    }

    #[verifier(external_body)]
    pub fn set_init_containers(&mut self, init_containers: Vec<Container>)
        ensures self@ == old(self)@.with_init_containers(init_containers.deep_view()),
    {
        self.inner.init_containers = Some(init_containers.into_iter().map(|container: Container| container.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_service_account_name(&mut self, service_account: String)
        ensures self@ == old(self)@.with_service_account_name(service_account@),
    {
        self.inner.service_account_name = Some(service_account)
    }

    #[verifier(external_body)]
    pub fn set_tolerations(&mut self, tolerations: Vec<Toleration>)
        ensures self@ == old(self)@.with_tolerations(tolerations.deep_view()),
    {
        self.inner.tolerations = Some(tolerations.into_iter().map(|toleration: Toleration| toleration.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_node_selector(&mut self, node_selector: StringMap)
        ensures self@ == old(self)@.with_node_selector(node_selector@),
    {
        self.inner.node_selector = Some(node_selector.into_rust_map())
    }

    #[verifier(external_body)]
    pub fn set_runtime_class_name(&mut self, runtime_class_name: String)
        ensures self@ == old(self)@.with_runtime_class_name(runtime_class_name@),
    {
        self.inner.runtime_class_name = Some(runtime_class_name)
    }

    #[verifier(external_body)]
    pub fn set_dns_policy(&mut self, dns_policy: String)
        ensures self@ == old(self)@.with_dns_policy(dns_policy@),
    {
        self.inner.dns_policy = Some(dns_policy)
    }

    #[verifier(external_body)]
    pub fn set_scheduler_name(&mut self, scheduler_name: String)
        ensures self@ == old(self)@.with_scheduler_name(scheduler_name@),
    {
        self.inner.scheduler_name = Some(scheduler_name)
    }

    #[verifier(external_body)]
    pub fn set_priority_class_name(&mut self, priority_class_name: String)
        ensures self@ == old(self)@.with_priority_class_name(priority_class_name@),
    {
        self.inner.priority_class_name = Some(priority_class_name)
    }

    #[verifier(external_body)]
    pub fn set_security_context(&mut self, security_context: PodSecurityContext)
        ensures self@ == old(self)@.with_security_context(security_context@),
    {
        self.inner.security_context = Some(security_context.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_host_network(&mut self, host_network: bool)
        ensures self@ == old(self)@.with_host_network(host_network),
    {
        self.inner.host_network = Some(host_network);
    }

    #[verifier(external_body)]
    pub fn set_termination_grace_period_seconds(&mut self, termination_grace_period_seconds: i64)
        ensures self@ == old(self)@.with_termination_grace_period_seconds(termination_grace_period_seconds as int),
    {
        self.inner.termination_grace_period_seconds = Some(termination_grace_period_seconds);
    }

    #[verifier(external_body)]
    pub fn set_image_pull_secrets(&mut self, image_pull_secrets: Vec<LocalObjectReference>)
        ensures self@ == old(self)@.with_image_pull_secrets(image_pull_secrets.deep_view()),
    {
        self.inner.image_pull_secrets = Some(image_pull_secrets.into_iter().map(|r: LocalObjectReference| r.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_hostname(&mut self, hostname: String) 
        ensures self@ == old(self)@.with_hostname(hostname@)
    {
        self.inner.hostname = Some(hostname);
    }

    #[verifier(external_body)]
    pub fn unset_hostname(&mut self)
        ensures self@ == old(self)@.without_hostname()
    {
        self.inner.hostname = None;
    }

    #[verifier(external_body)]
    pub fn set_subdomain(&mut self, subdomain: String)
        ensures self@ == old(self)@.with_subdomain(subdomain@)
    {
        self.inner.subdomain = Some(subdomain);
    }

    #[verifier(external_body)]
    pub fn unset_subdomain(&mut self)
        ensures self@ == old(self)@.without_subdomain()
    {
        self.inner.subdomain = None;
    }

    // TODO: fix this for VSTS controller
    #[verifier(external_body)]
    pub fn eq_spec(&self, other: &Self) -> (res: bool)
        ensures res == (self@ == other@)
    {
        true
    }
}

}
