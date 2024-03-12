// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::fluent_controller::fluentbit::trusted::{
    spec_types, spec_types::FluentBitView, step::*,
};
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    affinity::*, api_resource::*, container::*, dynamic::*, object_meta::*, owner_reference::*,
    prelude::*, resource::*, resource_requirements::*, toleration::*, volume::*,
};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

pub struct FluentBitReconcileState {
    pub reconcile_step: FluentBitReconcileStep,
}

impl std::clone::Clone for FluentBitReconcileState {
    #[verifier(external_body)]
    fn clone(&self) -> (result: FluentBitReconcileState)
        ensures result == self
    {
        FluentBitReconcileState {
            reconcile_step: self.reconcile_step,
        }
    }
}

impl View for FluentBitReconcileState {
    type V = spec_types::FluentBitReconcileState;
    open spec fn view(&self) -> spec_types::FluentBitReconcileState { spec_types::FluentBitReconcileState { reconcile_step: self.reconcile_step } }
}

#[verifier(external_body)]
pub struct FluentBit {
    inner: deps_hack::FluentBit
}

impl View for FluentBit {
    type V = FluentBitView;

    spec fn view(&self) -> FluentBitView;
}

impl FluentBit {
    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: FluentBitSpec)
        ensures spec@ == self@.spec,
    {
        FluentBitSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == FluentBitView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::FluentBit>(&()))
    }

    #[verifier(external_body)]
    pub fn controller_owner_ref(&self) -> (owner_reference: OwnerReference)
        ensures owner_reference@ == self@.controller_owner_ref(),
    {
        OwnerReference::from_kube(
            // We can safely unwrap here because the trait method implementation always returns a Some(...)
            self.inner.controller_owner_ref(&()).unwrap()
        )
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
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<FluentBit, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == FluentBitView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == FluentBitView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::FluentBit>();
        if parse_result.is_ok() {
            let res = FluentBit { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::FluentBit> for FluentBit {
    fn from_kube(inner: deps_hack::FluentBit) -> FluentBit { FluentBit { inner: inner } }

    fn into_kube(self) -> deps_hack::FluentBit { self.inner }
}

#[verifier(external_body)]
pub struct FluentBitSpec {
    inner: deps_hack::FluentBitSpec,
}

impl FluentBitSpec {
    pub spec fn view(&self) -> spec_types::FluentBitSpecView;

    #[verifier(external_body)]
    pub fn fluentbit_config_name(&self) -> (fluentbit_config_name: String)
        ensures fluentbit_config_name@ == self@.fluentbit_config_name,
    {
        String::from_rust_string(self.inner.fluentbit_config_name.to_string())
    }

    #[verifier(external_body)]
    pub fn image(&self) -> (image: String)
        ensures image@ == self@.image,
    {
        String::from_rust_string(self.inner.image.clone())
    }

    #[verifier(external_body)]
    pub fn resources(&self) -> (resources: Option<ResourceRequirements>)
        ensures
            self@.resources.is_Some() == resources.is_Some(),
            resources.is_Some() ==> resources.get_Some_0()@ == self@.resources.get_Some_0(),
    {
        match &self.inner.resources {
            Some(r) => Some(ResourceRequirements::from_kube(r.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn tolerations(&self) -> (tolerations: Option<Vec<Toleration>>)
        ensures
            self@.tolerations.is_Some() == tolerations.is_Some(),
            tolerations.is_Some() ==> tolerations.get_Some_0()@.map_values(|t: Toleration| t@) == self@.tolerations.get_Some_0(),
    {
        match &self.inner.tolerations {
            Some(tols) => Some(tols.clone().into_iter().map(|t: deps_hack::k8s_openapi::api::core::v1::Toleration| Toleration::from_kube(t)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn labels(&self) -> (labels: StringMap)
        ensures labels@ == self@.labels,
    {
        StringMap::from_rust_map(self.inner.labels.clone())
    }

    #[verifier(external_body)]
    pub fn annotations(&self) -> (annotations: StringMap)
        ensures annotations@ == self@.annotations,
    {
        StringMap::from_rust_map(self.inner.annotations.clone())
    }

    #[verifier(external_body)]
    pub fn service_account_annotations(&self) -> (service_account_annotations: StringMap)
        ensures service_account_annotations@ == self@.service_account_annotations,
    {
        StringMap::from_rust_map(self.inner.service_account_annotations.clone())
    }

    #[verifier(external_body)]
    pub fn service_labels(&self) -> (service_labels: StringMap)
        ensures service_labels@ == self@.service_labels,
    {
        StringMap::from_rust_map(self.inner.service_labels.clone())
    }

    #[verifier(external_body)]
    pub fn service_selector(&self) -> (service_selector: Option<StringMap>)
        ensures
            service_selector.is_Some() == self@.service_selector.is_Some(),
            service_selector.is_Some() ==> service_selector.get_Some_0()@ == self@.service_selector.get_Some_0(),
    {
        match &self.inner.service_selector {
            Some(selector) => Some(StringMap::from_rust_map(selector.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn service_annotations(&self) -> (service_annotations: StringMap)
        ensures service_annotations@ == self@.service_annotations,
    {
        StringMap::from_rust_map(self.inner.service_annotations.clone())
    }

    #[verifier(external_body)]
    pub fn affinity(&self) -> (affinity: Option<Affinity>)
        ensures
            self@.affinity.is_Some() == affinity.is_Some(),
            affinity.is_Some() ==> affinity.get_Some_0()@ == self@.affinity.get_Some_0(),
    {
        match &self.inner.affinity {
            Some(a) => Some(Affinity::from_kube(a.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn disable_log_volumes(&self) -> (disable_log_volumes: bool)
        ensures disable_log_volumes == self@.disable_log_volumes,
    {
        self.inner.disable_log_volumes
    }

    #[verifier(external_body)]
    pub fn node_selector(&self) -> (node_selector: StringMap)
        ensures node_selector@ == self@.node_selector,
    {
        StringMap::from_rust_map(self.inner.node_selector.clone())
    }

    #[verifier(external_body)]
    pub fn runtime_class_name(&self) -> (runtime_class_name: Option<String>)
        ensures opt_string_to_view(&runtime_class_name) == self@.runtime_class_name,
    {
        match &self.inner.runtime_class_name {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn dns_policy(&self) -> (dns_policy: Option<String>)
        ensures opt_string_to_view(&dns_policy) == self@.dns_policy,
    {
        match &self.inner.dns_policy {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn priority_class_name(&self) -> (priority_class_name: Option<String>)
        ensures opt_string_to_view(&priority_class_name) == self@.priority_class_name,
    {
        match &self.inner.priority_class_name {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn volumes(&self) -> (volumes: Option<Vec<Volume>>)
        ensures
            self@.volumes.is_Some() == volumes.is_Some(),
            volumes.is_Some() ==> volumes.get_Some_0()@.map_values(|v: Volume| v@) == self@.volumes.get_Some_0(),
    {
        match &self.inner.volumes {
            Some(volumes) => Some(volumes.clone().into_iter().map(|v: deps_hack::k8s_openapi::api::core::v1::Volume| Volume::from_kube(v)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn volume_mounts(&self) -> (volume_mounts: Option<Vec<VolumeMount>>)
        ensures
            self@.volume_mounts.is_Some() == volume_mounts.is_Some(),
            volume_mounts.is_Some() ==> volume_mounts.get_Some_0()@.map_values(|v: VolumeMount| v@) == self@.volume_mounts.get_Some_0(),
    {
        match &self.inner.volume_mounts {
            Some(volume_mounts) => Some(volume_mounts.clone().into_iter().map(|v: deps_hack::k8s_openapi::api::core::v1::VolumeMount| VolumeMount::from_kube(v)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn scheduler_name(&self) -> (scheduler_name: Option<String>)
        ensures opt_string_to_view(&scheduler_name) == self@.scheduler_name,
    {
        match &self.inner.scheduler_name {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn metrics_port(&self) -> (metrics_port: Option<i32>)
        ensures
            metrics_port.is_Some() == self@.metrics_port.is_Some(),
            metrics_port.is_Some() ==> metrics_port.get_Some_0() as int == self@.metrics_port.get_Some_0(),
    {
        self.inner.metrics_port
    }

    #[verifier(external_body)]
    pub fn internal_mount_propagation(&self) -> (internal_mount_propagation: Option<String>)
        ensures opt_string_to_view(&internal_mount_propagation) == self@.internal_mount_propagation,
    {
        match &self.inner.internal_mount_propagation {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn position_db(&self) -> (position_db: Option<HostPathVolumeSource>)
        ensures
            position_db.is_Some() == self@.position_db.is_Some(),
            position_db.is_Some() ==> position_db.get_Some_0()@ == self@.position_db.get_Some_0(),
    {
        match &self.inner.position_db {
            Some(p) => Some(HostPathVolumeSource::from_kube(p.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn container_log_real_path(&self) -> (container_log_real_path: Option<String>)
        ensures opt_string_to_view(&container_log_real_path) == self@.container_log_real_path,
    {
        match &self.inner.container_log_real_path {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn security_context(&self) -> (security_context: Option<PodSecurityContext>)
        ensures
            security_context.is_Some() == self@.security_context.is_Some(),
            security_context.is_Some() ==> security_context.get_Some_0()@ == self@.security_context.get_Some_0(),
    {
        match &self.inner.security_context {
            Some(s) => Some(PodSecurityContext::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn container_security_context(&self) -> (container_security_context: Option<SecurityContext>)
        ensures
            container_security_context.is_Some() == self@.container_security_context.is_Some(),
            container_security_context.is_Some() ==> container_security_context.get_Some_0()@ == self@.container_security_context.get_Some_0(),
    {
        match &self.inner.container_security_context {
            Some(s) => Some(SecurityContext::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn host_network(&self) -> (host_network: Option<bool>)
        ensures host_network == self@.host_network,
    {
        self.inner.host_network
    }

    #[verifier(external_body)]
    pub fn args(&self) -> (args: Option<Vec<String>>)
        ensures
            args.is_Some() == self@.args.is_Some(),
            args.is_Some() ==> args.get_Some_0()@.map_values(|s: String| s@) == self@.args.get_Some_0(),
    {
        match &self.inner.args {
            Some(arguments) => Some(arguments.clone().into_iter().map(|s: std::string::String| String::from_rust_string(s)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn command(&self) -> (command: Option<Vec<String>>)
        ensures
            command.is_Some() == self@.command.is_Some(),
            command.is_Some() ==> command.get_Some_0()@.map_values(|s: String| s@) == self@.command.get_Some_0(),
    {
        match &self.inner.command {
            Some(cmd) => Some(cmd.clone().into_iter().map(|s: std::string::String| String::from_rust_string(s)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn env_vars(&self) -> (env_vars: Option<Vec<EnvVar>>)
        ensures
            env_vars.is_Some() == self@.env_vars.is_Some(),
            env_vars.is_Some() ==> env_vars.get_Some_0()@.map_values(|var: EnvVar| var@) == self@.env_vars.get_Some_0(),
    {
        match &self.inner.env_vars {
            Some(env_vars) => Some(env_vars.clone().into_iter().map(|e: deps_hack::k8s_openapi::api::core::v1::EnvVar| EnvVar::from_kube(e)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn image_pull_policy(&self) -> (image_pull_policy: Option<String>)
        ensures opt_string_to_view(&image_pull_policy) == self@.image_pull_policy,
    {
        match &self.inner.image_pull_policy {
            Some(n) => Some(String::from_rust_string(n.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn image_pull_secrets(&self) -> (image_pull_secrets: Option<Vec<LocalObjectReference>>)
        ensures
            self@.image_pull_secrets.is_Some() == image_pull_secrets.is_Some(),
            image_pull_secrets.is_Some() ==> image_pull_secrets.get_Some_0()@.map_values(|t: LocalObjectReference| t@) == self@.image_pull_secrets.get_Some_0(),
    {
        match &self.inner.image_pull_secrets {
            Some(secrets) => Some(secrets.clone().into_iter().map(|t: deps_hack::k8s_openapi::api::core::v1::LocalObjectReference| LocalObjectReference::from_kube(t)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn liveness_probe(&self) -> (liveness_probe: Option<Probe>)
        ensures
            liveness_probe.is_Some() == self@.liveness_probe.is_Some(),
            liveness_probe.is_Some() ==> liveness_probe.get_Some_0()@ == self@.liveness_probe.get_Some_0(),
    {
        match &self.inner.liveness_probe {
            Some(s) => Some(Probe::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn readiness_probe(&self) -> (readiness_probe: Option<Probe>)
        ensures
            readiness_probe.is_Some() == self@.readiness_probe.is_Some(),
            readiness_probe.is_Some() ==> readiness_probe.get_Some_0()@ == self@.readiness_probe.get_Some_0(),
    {
        match &self.inner.readiness_probe {
            Some(s) => Some(Probe::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn init_containers(&self) -> (init_containers: Option<Vec<Container>>)
        ensures
            self@.init_containers.is_Some() == init_containers.is_Some(),
            init_containers.is_Some() ==> init_containers.get_Some_0()@.map_values(|c: Container| c@) == self@.init_containers.get_Some_0(),
    {
        match &self.inner.init_containers {
            Some(containers) => Some(containers.clone().into_iter().map(|c: deps_hack::k8s_openapi::api::core::v1::Container| Container::from_kube(c)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn ports(&self) -> (ports: Option<Vec<ContainerPort>>)
        ensures
            self@.ports.is_Some() == ports.is_Some(),
            ports.is_Some() ==> ports.get_Some_0()@.map_values(|c: ContainerPort| c@) == self@.ports.get_Some_0(),
    {
        match &self.inner.ports {
            Some(ports) => Some(ports.clone().into_iter().map(|c: deps_hack::k8s_openapi::api::core::v1::ContainerPort| ContainerPort::from_kube(c)).collect()),
            None => None,
        }
    }
}

}
