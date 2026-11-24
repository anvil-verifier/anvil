use std::collections::btree_map::Keys;

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
use tracing::{error, info, warn};
use k8s_openapi::api::core::v1 as k8s_types;

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

implement_object_wrapper_type!(Pod, k8s_openapi::api::core::v1::Pod, PodView);

implement_field_wrapper_type!(
    PodSpec,
    k8s_openapi::api::core::v1::PodSpec,
    PodSpecView
);

implement_field_wrapper_type!(
    PodSecurityContext,
    k8s_openapi::api::core::v1::PodSecurityContext,
    PodSecurityContextView
);

implement_field_wrapper_type!(
    LocalObjectReference,
    k8s_openapi::api::core::v1::LocalObjectReference,
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
        ensures final(self)@ == old(self)@.with_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }
}

#[verifier::external]
#[verifier::external]
fn eq_opt_string(a: &Option<String>, b: &Option<String>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(sa), Some(sb)) => sa == sb,
        _ => false,
    }
}

#[verifier::external]
fn eq_string_vec(a: &Vec<String>, b: &Vec<String>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

#[verifier::external]
fn eq_opt_string_vec(a: &Option<Vec<String>>, b: &Option<Vec<String>>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => eq_string_vec(va, vb),
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_field_ref(
    a: &Option<k8s_types::ObjectFieldSelector>,
    b: &Option<k8s_types::ObjectFieldSelector>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(fa), Some(fb)) => {
            fa.field_path == fb.field_path && eq_opt_string(&fa.api_version, &fb.api_version)
        }
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_exec_action(
    a: &Option<k8s_types::ExecAction>,
    b: &Option<k8s_types::ExecAction>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(ea), Some(eb)) => eq_opt_string_vec(&ea.command, &eb.command),
        _ => false,
    }
}

#[verifier::external]
fn eq_int_or_string(
    a: &k8s_openapi::apimachinery::pkg::util::intstr::IntOrString,
    b: &k8s_openapi::apimachinery::pkg::util::intstr::IntOrString,
) -> bool {
    match (a, b) {
        (
            k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(ia),
            k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(ib),
        ) => *ia == *ib,
        (
            k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::String(sa),
            k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::String(sb),
        ) => sa == sb,
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_probe(a: &Option<k8s_types::Probe>, b: &Option<k8s_types::Probe>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(pa), Some(pb)) => {
            eq_opt_exec_action(&pa.exec, &pb.exec)
                && pa.failure_threshold == pb.failure_threshold
                && pa.initial_delay_seconds == pb.initial_delay_seconds
                && pa.period_seconds == pb.period_seconds
                && pa.success_threshold == pb.success_threshold
                && pa.timeout_seconds == pb.timeout_seconds
                && match (&pa.tcp_socket, &pb.tcp_socket) {
                    (None, None) => true,
                    (Some(ta), Some(tb)) => {
                        eq_opt_string(&ta.host, &tb.host) && eq_int_or_string(&ta.port, &tb.port)
                    }
                    _ => false,
                }
        }
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_env_vars(a: &Option<Vec<k8s_types::EnvVar>>, b: &Option<Vec<k8s_types::EnvVar>>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => {
            if va.len() != vb.len() {
                return false;
            }
            let mut i: usize = 0;
            while i < va.len() {
                let e1 = &va[i];
                let e2 = &vb[i];
                let vf_eq = match (&e1.value_from, &e2.value_from) {
                    (None, None) => true,
                    (Some(vf1), Some(vf2)) => eq_opt_field_ref(&vf1.field_ref, &vf2.field_ref),
                    _ => false,
                };
                if e1.name != e2.name || !eq_opt_string(&e1.value, &e2.value) || !vf_eq {
                    return false;
                }
                i += 1;
            }
            true
        }
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_ports(
    a: &Option<Vec<k8s_types::ContainerPort>>,
    b: &Option<Vec<k8s_types::ContainerPort>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => {
            if va.len() != vb.len() {
                return false;
            }
            let mut i: usize = 0;
            while i < va.len() {
                let p1 = &va[i];
                let p2 = &vb[i];
                if p1.container_port != p2.container_port
                    || !eq_opt_string(&p1.name, &p2.name)
                    || !eq_opt_string(&p1.protocol, &p2.protocol)
                {
                    return false;
                }
                i += 1;
            }
            true
        }
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_volume_mounts(
    a: &Option<Vec<k8s_types::VolumeMount>>,
    b: &Option<Vec<k8s_types::VolumeMount>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => {
            if va.len() != vb.len() {
                return false;
            }
            let mut i: usize = 0;
            while i < va.len() {
                let m1 = &va[i];
                let m2 = &vb[i];
                if m1.mount_path != m2.mount_path
                    || m1.name != m2.name
                    || m1.read_only != m2.read_only
                    || !eq_opt_string(&m1.sub_path, &m2.sub_path)
                    || !eq_opt_string(&m1.mount_propagation, &m2.mount_propagation)
                {
                    return false;
                }
                i += 1;
            }
            true
        }
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_lifecycle(a: &Option<k8s_types::Lifecycle>, b: &Option<k8s_types::Lifecycle>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(l1), Some(l2)) => match (&l1.pre_stop, &l2.pre_stop) {
            (None, None) => true,
            (Some(ps1), Some(ps2)) => eq_opt_exec_action(&ps1.exec, &ps2.exec),
            _ => false,
        },
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_resources(
    a: &Option<k8s_types::ResourceRequirements>,
    b: &Option<k8s_types::ResourceRequirements>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(r1), Some(r2)) => r1.limits == r2.limits && r1.requests == r2.requests,
        _ => false,
    }
}

#[verifier::external]
fn eq_container(c1: &k8s_types::Container, c2: &k8s_types::Container) -> bool {
    c1.name == c2.name
        && eq_opt_string(&c1.image, &c2.image)
        && eq_opt_string_vec(&c1.command, &c2.command)
        && eq_opt_string_vec(&c1.args, &c2.args)
        && eq_opt_string(&c1.image_pull_policy, &c2.image_pull_policy)
        && (c1.security_context.is_some() == c2.security_context.is_some())
        && eq_opt_env_vars(&c1.env, &c2.env)
        && eq_opt_ports(&c1.ports, &c2.ports)
        && eq_opt_volume_mounts(&c1.volume_mounts, &c2.volume_mounts)
        && eq_opt_lifecycle(&c1.lifecycle, &c2.lifecycle)
        && eq_opt_resources(&c1.resources, &c2.resources)
        && eq_opt_probe(&c1.readiness_probe, &c2.readiness_probe)
        && eq_opt_probe(&c1.liveness_probe, &c2.liveness_probe)
}

#[verifier::external]
fn eq_containers(a: &Vec<k8s_types::Container>, b: &Vec<k8s_types::Container>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len() {
        if !eq_container(&a[i], &b[i]) {
            return false;
        }
        i += 1;
    }
    true
}

#[verifier::external]
fn eq_opt_containers(
    a: &Option<Vec<k8s_types::Container>>,
    b: &Option<Vec<k8s_types::Container>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => eq_containers(va, vb),
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_key_to_paths(
    a: &Option<Vec<k8s_types::KeyToPath>>,
    b: &Option<Vec<k8s_types::KeyToPath>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => {
            if va.len() != vb.len() {
                return false;
            }
            let mut i: usize = 0;
            while i < va.len() {
                if va[i].key != vb[i].key || va[i].path != vb[i].path {
                    return false;
                }
                i += 1;
            }
            true
        }
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_downward_items(
    a: &Option<Vec<k8s_types::DownwardAPIVolumeFile>>,
    b: &Option<Vec<k8s_types::DownwardAPIVolumeFile>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => {
            if va.len() != vb.len() {
                return false;
            }
            let mut i: usize = 0;
            while i < va.len() {
                if va[i].path != vb[i].path
                    || !eq_opt_field_ref(&va[i].field_ref, &vb[i].field_ref)
                {
                    return false;
                }
                i += 1;
            }
            true
        }
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_volume_projections(
    a: &Option<Vec<k8s_types::VolumeProjection>>,
    b: &Option<Vec<k8s_types::VolumeProjection>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => {
            if va.len() != vb.len() {
                return false;
            }
            let mut i: usize = 0;
            while i < va.len() {
                let s1 = &va[i];
                let s2 = &vb[i];
                let cm_eq = match (&s1.config_map, &s2.config_map) {
                    (None, None) => true,
                    (Some(c1), Some(c2)) => {
                        eq_opt_string(&c1.name, &c2.name)
                            && eq_opt_key_to_paths(&c1.items, &c2.items)
                    }
                    _ => false,
                };
                let sec_eq = match (&s1.secret, &s2.secret) {
                    (None, None) => true,
                    (Some(c1), Some(c2)) => {
                        eq_opt_string(&c1.name, &c2.name)
                            && eq_opt_key_to_paths(&c1.items, &c2.items)
                    }
                    _ => false,
                };
                if !cm_eq || !sec_eq {
                    return false;
                }
                i += 1;
            }
            true
        }
        _ => false,
    }
}

#[verifier::external]
fn eq_volume(v1: &k8s_types::Volume, v2: &k8s_types::Volume) -> bool {
    let hp_eq = match (&v1.host_path, &v2.host_path) {
        (None, None) => true,
        (Some(a), Some(b)) => a.path == b.path,
        _ => false,
    };
    let cm_eq = match (&v1.config_map, &v2.config_map) {
        (None, None) => true,
        (Some(a), Some(b)) => eq_opt_string(&a.name, &b.name),
        _ => false,
    };
    let sec_eq = match (&v1.secret, &v2.secret) {
        (None, None) => true,
        (Some(a), Some(b)) => eq_opt_string(&a.secret_name, &b.secret_name),
        _ => false,
    };
    let ed_eq = match (&v1.empty_dir, &v2.empty_dir) {
        (None, None) => true,
        (Some(a), Some(b)) => {
            eq_opt_string(&a.medium, &b.medium)
                && match (&a.size_limit, &b.size_limit) {
                    (None, None) => true,
                    (Some(qa), Some(qb)) => qa.0 == qb.0,
                    _ => false,
                }
        }
        _ => false,
    };
    let pvc_eq = match (&v1.persistent_volume_claim, &v2.persistent_volume_claim) {
        (None, None) => true,
        (Some(a), Some(b)) => a.claim_name == b.claim_name && a.read_only == b.read_only,
        _ => false,
    };
    let da_eq = match (&v1.downward_api, &v2.downward_api) {
        (None, None) => true,
        (Some(a), Some(b)) => eq_opt_downward_items(&a.items, &b.items),
        _ => false,
    };
    let proj_eq = match (&v1.projected, &v2.projected) {
        (None, None) => true,
        (Some(a), Some(b)) => eq_opt_volume_projections(&a.sources, &b.sources),
        _ => false,
    };
    v1.name == v2.name && hp_eq && cm_eq && sec_eq && ed_eq && pvc_eq && da_eq && proj_eq
}

#[verifier::external]
fn eq_opt_volumes(a: &Option<Vec<k8s_types::Volume>>, b: &Option<Vec<k8s_types::Volume>>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => {
            if va.len() != vb.len() {
                return false;
            }
            let mut i: usize = 0;
            while i < va.len() {
                if !eq_volume(&va[i], &vb[i]) {
                    return false;
                }
                i += 1;
            }
            true
        }
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_tolerations_len(
    a: &Option<Vec<k8s_types::Toleration>>,
    b: &Option<Vec<k8s_types::Toleration>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => va.len() == vb.len(),
        _ => false,
    }
}

#[verifier::external]
fn eq_opt_local_obj_refs_len(
    a: &Option<Vec<k8s_types::LocalObjectReference>>,
    b: &Option<Vec<k8s_types::LocalObjectReference>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(va), Some(vb)) => va.len() == vb.len(),
        _ => false,
    }
}

impl PodSpec {
    #[verifier(external_body)]
    pub fn set_affinity(&mut self, affinity: Affinity)
        ensures final(self)@ == old(self)@.with_affinity(affinity@),
    {
        self.inner.affinity = Some(affinity.into_kube())
    }

    #[verifier(external_body)]
    pub fn set_containers(&mut self, containers: Vec<Container>)
        ensures final(self)@ == old(self)@.with_containers(containers.deep_view()),
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
        ensures final(self)@ == old(self)@.with_volumes(volumes.deep_view()),
    {
        self.inner.volumes = Some(volumes.into_iter().map(|vol: Volume| vol.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn unset_volumes(&mut self)
        ensures final(self)@ == old(self)@.without_volumes(),
    {
        self.inner.volumes = None;
    }

    #[verifier(external_body)]
    pub fn set_init_containers(&mut self, init_containers: Vec<Container>)
        ensures final(self)@ == old(self)@.with_init_containers(init_containers.deep_view()),
    {
        self.inner.init_containers = Some(init_containers.into_iter().map(|container: Container| container.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_service_account_name(&mut self, service_account: String)
        ensures final(self)@ == old(self)@.with_service_account_name(service_account@),
    {
        self.inner.service_account_name = Some(service_account)
    }

    #[verifier(external_body)]
    pub fn set_tolerations(&mut self, tolerations: Vec<Toleration>)
        ensures final(self)@ == old(self)@.with_tolerations(tolerations.deep_view()),
    {
        self.inner.tolerations = Some(tolerations.into_iter().map(|toleration: Toleration| toleration.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_node_selector(&mut self, node_selector: StringMap)
        ensures final(self)@ == old(self)@.with_node_selector(node_selector@),
    {
        self.inner.node_selector = Some(node_selector.into_rust_map())
    }

    #[verifier(external_body)]
    pub fn set_runtime_class_name(&mut self, runtime_class_name: String)
        ensures final(self)@ == old(self)@.with_runtime_class_name(runtime_class_name@),
    {
        self.inner.runtime_class_name = Some(runtime_class_name)
    }

    #[verifier(external_body)]
    pub fn set_dns_policy(&mut self, dns_policy: String)
        ensures final(self)@ == old(self)@.with_dns_policy(dns_policy@),
    {
        self.inner.dns_policy = Some(dns_policy)
    }

    #[verifier(external_body)]
    pub fn set_scheduler_name(&mut self, scheduler_name: String)
        ensures final(self)@ == old(self)@.with_scheduler_name(scheduler_name@),
    {
        self.inner.scheduler_name = Some(scheduler_name)
    }

    #[verifier(external_body)]
    pub fn set_priority_class_name(&mut self, priority_class_name: String)
        ensures final(self)@ == old(self)@.with_priority_class_name(priority_class_name@),
    {
        self.inner.priority_class_name = Some(priority_class_name)
    }

    #[verifier(external_body)]
    pub fn set_security_context(&mut self, security_context: PodSecurityContext)
        ensures final(self)@ == old(self)@.with_security_context(security_context@),
    {
        self.inner.security_context = Some(security_context.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_host_network(&mut self, host_network: bool)
        ensures final(self)@ == old(self)@.with_host_network(host_network),
    {
        self.inner.host_network = Some(host_network);
    }

    #[verifier(external_body)]
    pub fn set_termination_grace_period_seconds(&mut self, termination_grace_period_seconds: i64)
        ensures final(self)@ == old(self)@.with_termination_grace_period_seconds(termination_grace_period_seconds as int),
    {
        self.inner.termination_grace_period_seconds = Some(termination_grace_period_seconds);
    }

    #[verifier(external_body)]
    pub fn set_image_pull_secrets(&mut self, image_pull_secrets: Vec<LocalObjectReference>)
        ensures final(self)@ == old(self)@.with_image_pull_secrets(image_pull_secrets.deep_view()),
    {
        self.inner.image_pull_secrets = Some(image_pull_secrets.into_iter().map(|r: LocalObjectReference| r.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn hostname(&self) -> (hostname: Option<String>)
        ensures hostname.deep_view() == self@.hostname
    {
        self.inner.hostname.clone()
    }

    #[verifier(external_body)]
    pub fn set_hostname(&mut self, hostname: String)
        ensures final(self)@ == old(self)@.with_hostname(hostname@)
    {
        self.inner.hostname = Some(hostname);
    }

    #[verifier(external_body)]
    pub fn unset_hostname(&mut self)
        ensures final(self)@ == old(self)@.without_hostname()
    {
        self.inner.hostname = None;
    }

    #[verifier(external_body)]
    pub fn subdomain(&self) -> (subdomain: Option<String>)
        ensures subdomain.deep_view() == self@.subdomain
    {
        self.inner.subdomain.clone()
    }

    #[verifier(external_body)]
    pub fn set_subdomain(&mut self, subdomain: String)
        ensures final(self)@ == old(self)@.with_subdomain(subdomain@)
    {
        self.inner.subdomain = Some(subdomain);
    }

    #[verifier(external_body)]
    pub fn unset_subdomain(&mut self)
        ensures final(self)@ == old(self)@.without_subdomain()
    {
        self.inner.subdomain = None;
    }

    #[verifier(external_body)]
    pub fn eq_spec(&self, other: &Self) -> (res: bool)
        ensures res == (self@ == other@)
    {
        (self.inner.affinity.is_some() == other.inner.affinity.is_some())
            && eq_containers(&self.inner.containers, &other.inner.containers)
            && eq_opt_volumes(&self.inner.volumes, &other.inner.volumes)
            && eq_opt_containers(&self.inner.init_containers, &other.inner.init_containers)
            && eq_opt_string(
                &self.inner.service_account_name,
                &other.inner.service_account_name,
            )
            && eq_opt_tolerations_len(&self.inner.tolerations, &other.inner.tolerations)
            && self.inner.node_selector == other.inner.node_selector
            && eq_opt_string(
                &self.inner.runtime_class_name,
                &other.inner.runtime_class_name,
            )
            && eq_opt_string(&self.inner.dns_policy, &other.inner.dns_policy)
            && eq_opt_string(
                &self.inner.priority_class_name,
                &other.inner.priority_class_name,
            )
            && eq_opt_string(&self.inner.scheduler_name, &other.inner.scheduler_name)
            && (self.inner.security_context.is_some() == other.inner.security_context.is_some())
            && self.inner.host_network == other.inner.host_network
            && self.inner.termination_grace_period_seconds
                == other.inner.termination_grace_period_seconds
            && eq_opt_local_obj_refs_len(
                &self.inner.image_pull_secrets,
                &other.inner.image_pull_secrets,
            )
            && eq_opt_string(&self.inner.hostname, &other.inner.hostname)
            && eq_opt_string(&self.inner.subdomain, &other.inner.subdomain)
    }
}

}
