// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::fluent_controller::fluentbit::trusted::{
    spec_types, spec_types::FluentBitView, step::*,
};
use crate::kubernetes_api_objects::error::UnmarshalError;
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

    uninterp spec fn view(&self) -> FluentBitView;
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
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<FluentBit, UnmarshalError>)
        ensures
            res.is_Ok() == FluentBitView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == FluentBitView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::FluentBit>();
        if parse_result.is_ok() {
            let res = FluentBit { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(())
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
    pub uninterp spec fn view(&self) -> spec_types::FluentBitSpecView;

    #[verifier(external_body)]
    pub fn fluentbit_config_name(&self) -> (fluentbit_config_name: String)
        ensures fluentbit_config_name@ == self@.fluentbit_config_name,
    {
        self.inner.fluentbit_config_name.clone()
    }

    #[verifier(external_body)]
    pub fn image(&self) -> (image: String)
        ensures image@ == self@.image,
    {
        self.inner.image.clone()
    }

    #[verifier(external_body)]
    pub fn resources(&self) -> (resources: Option<ResourceRequirements>)
        ensures
            self@.resources is Some == resources is Some,
            resources is Some ==> resources->0@ == self@.resources->0,
    {
        match &self.inner.resources {
            Some(r) => Some(ResourceRequirements::from_kube(r.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn tolerations(&self) -> (tolerations: Option<Vec<Toleration>>)
        ensures
            self@.tolerations is Some == tolerations is Some,
            tolerations is Some ==> tolerations->0@.map_values(|t: Toleration| t@) == self@.tolerations->0,
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
            service_selector is Some == self@.service_selector is Some,
            service_selector is Some ==> service_selector->0@ == self@.service_selector->0,
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
            self@.affinity is Some == affinity is Some,
            affinity is Some ==> affinity->0@ == self@.affinity->0,
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
        self.inner.runtime_class_name.clone()
    }

    #[verifier(external_body)]
    pub fn dns_policy(&self) -> (dns_policy: Option<String>)
        ensures opt_string_to_view(&dns_policy) == self@.dns_policy,
    {
        self.inner.dns_policy.clone()
    }

    #[verifier(external_body)]
    pub fn priority_class_name(&self) -> (priority_class_name: Option<String>)
        ensures opt_string_to_view(&priority_class_name) == self@.priority_class_name,
    {
        self.inner.priority_class_name.clone()
    }

    #[verifier(external_body)]
    pub fn volumes(&self) -> (volumes: Option<Vec<Volume>>)
        ensures
            self@.volumes is Some == volumes is Some,
            volumes is Some ==> volumes->0@.map_values(|v: Volume| v@) == self@.volumes->0,
    {
        match &self.inner.volumes {
            Some(volumes) => Some(volumes.clone().into_iter().map(|v: deps_hack::k8s_openapi::api::core::v1::Volume| Volume::from_kube(v)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn volume_mounts(&self) -> (volume_mounts: Option<Vec<VolumeMount>>)
        ensures
            self@.volume_mounts is Some == volume_mounts is Some,
            volume_mounts is Some ==> volume_mounts->0@.map_values(|v: VolumeMount| v@) == self@.volume_mounts->0,
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
        self.inner.scheduler_name.clone()
    }

    #[verifier(external_body)]
    pub fn metrics_port(&self) -> (metrics_port: Option<i32>)
        ensures
            metrics_port is Some == self@.metrics_port is Some,
            metrics_port is Some ==> metrics_port->0 as int == self@.metrics_port->0,
    {
        self.inner.metrics_port
    }

    #[verifier(external_body)]
    pub fn internal_mount_propagation(&self) -> (internal_mount_propagation: Option<String>)
        ensures opt_string_to_view(&internal_mount_propagation) == self@.internal_mount_propagation,
    {
        self.inner.internal_mount_propagation.clone()
    }

    #[verifier(external_body)]
    pub fn position_db(&self) -> (position_db: Option<HostPathVolumeSource>)
        ensures
            position_db is Some == self@.position_db is Some,
            position_db is Some ==> position_db->0@ == self@.position_db->0,
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
        self.inner.container_log_real_path.clone()
    }

    #[verifier(external_body)]
    pub fn security_context(&self) -> (security_context: Option<PodSecurityContext>)
        ensures
            security_context is Some == self@.security_context is Some,
            security_context is Some ==> security_context->0@ == self@.security_context->0,
    {
        match &self.inner.security_context {
            Some(s) => Some(PodSecurityContext::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn container_security_context(&self) -> (container_security_context: Option<SecurityContext>)
        ensures
            container_security_context is Some == self@.container_security_context is Some,
            container_security_context is Some ==> container_security_context->0@ == self@.container_security_context->0,
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
            args is Some == self@.args is Some,
            args is Some ==> args->0@.map_values(|s: String| s@) == self@.args->0,
    {
        self.inner.args.clone()
    }

    #[verifier(external_body)]
    pub fn command(&self) -> (command: Option<Vec<String>>)
        ensures
            command is Some == self@.command is Some,
            command is Some ==> command->0@.map_values(|s: String| s@) == self@.command->0,
    {
        self.inner.command.clone()
    }

    #[verifier(external_body)]
    pub fn env_vars(&self) -> (env_vars: Option<Vec<EnvVar>>)
        ensures
            env_vars is Some == self@.env_vars is Some,
            env_vars is Some ==> env_vars->0@.map_values(|var: EnvVar| var@) == self@.env_vars->0,
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
        self.inner.image_pull_policy.clone()
    }

    #[verifier(external_body)]
    pub fn image_pull_secrets(&self) -> (image_pull_secrets: Option<Vec<LocalObjectReference>>)
        ensures
            self@.image_pull_secrets is Some == image_pull_secrets is Some,
            image_pull_secrets is Some ==> image_pull_secrets->0@.map_values(|t: LocalObjectReference| t@) == self@.image_pull_secrets->0,
    {
        match &self.inner.image_pull_secrets {
            Some(secrets) => Some(secrets.clone().into_iter().map(|t: deps_hack::k8s_openapi::api::core::v1::LocalObjectReference| LocalObjectReference::from_kube(t)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn liveness_probe(&self) -> (liveness_probe: Option<Probe>)
        ensures
            liveness_probe is Some == self@.liveness_probe is Some,
            liveness_probe is Some ==> liveness_probe->0@ == self@.liveness_probe->0,
    {
        match &self.inner.liveness_probe {
            Some(s) => Some(Probe::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn readiness_probe(&self) -> (readiness_probe: Option<Probe>)
        ensures
            readiness_probe is Some == self@.readiness_probe is Some,
            readiness_probe is Some ==> readiness_probe->0@ == self@.readiness_probe->0,
    {
        match &self.inner.readiness_probe {
            Some(s) => Some(Probe::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn init_containers(&self) -> (init_containers: Option<Vec<Container>>)
        ensures
            self@.init_containers is Some == init_containers is Some,
            init_containers is Some ==> init_containers->0@.map_values(|c: Container| c@) == self@.init_containers->0,
    {
        match &self.inner.init_containers {
            Some(containers) => Some(containers.clone().into_iter().map(|c: deps_hack::k8s_openapi::api::core::v1::Container| Container::from_kube(c)).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn ports(&self) -> (ports: Option<Vec<ContainerPort>>)
        ensures
            self@.ports is Some == ports is Some,
            ports is Some ==> ports->0@.map_values(|c: ContainerPort| c@) == self@.ports->0,
    {
        match &self.inner.ports {
            Some(ports) => Some(ports.clone().into_iter().map(|c: deps_hack::k8s_openapi::api::core::v1::ContainerPort| ContainerPort::from_kube(c)).collect()),
            None => None,
        }
    }
}

}
