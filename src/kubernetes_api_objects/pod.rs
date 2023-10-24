// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    affinity::*, api_resource::*, common::*, container::*, dynamic::*,
    error::ParseDynamicObjectError, marshal::*, object_meta::*, resource::*,
    resource_requirements::*, toleration::*, volume::*,
};
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
        ensures
            pod@ == PodView::default(),
    {
        Pod {
            inner: deps_hack::k8s_openapi::api::core::v1::Pod::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
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
        ensures
            self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: PodSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Pod {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == PodView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::Pod>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
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
        ensures
            pod_spec@ == PodSpecView::default(),
    {
        PodSpec {
            inner: deps_hack::k8s_openapi::api::core::v1::PodSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (p: PodSpec)
        ensures
            p@ == self@,
    {
        PodSpec { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_affinity(&mut self, affinity: Affinity)
        ensures
            self@ == old(self)@.set_affinity(affinity@),
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
            Some(a) => {
                self.inner.affinity = Some(a.into_kube())
            },
            None => {
                self.inner.affinity = None
            }
        }
    }

    #[verifier(external_body)]
    pub fn set_containers(&mut self, containers: Vec<Container>)
        ensures
            self@ == old(self)@.set_containers(containers@.map_values(|container: Container| container@)),
    {
        self.inner.containers = containers.into_iter().map(|container: Container| container.into_kube()).collect()
    }

    #[verifier(external_body)]
    pub fn set_volumes(&mut self, volumes: Vec<Volume>)
        ensures
            self@ == old(self)@.set_volumes(volumes@.map_values(|vol: Volume| vol@)),
    {
        self.inner.volumes = Some(volumes.into_iter().map(|vol: Volume| vol.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_init_containers(&mut self, init_containers: Vec<Container>)
        ensures
            self@ == old(self)@.set_init_containers(init_containers@.map_values(|container: Container| container@)),
    {
        self.inner.init_containers = Some(init_containers.into_iter().map(|container: Container| container.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn set_service_account_name(&mut self, service_account: String)
        ensures
            self@ == old(self)@.set_service_account_name(service_account@),
    {
        self.inner.service_account_name = Some(service_account.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn set_tolerations(&mut self, tolerations: Vec<Toleration>)
        ensures
            self@ == old(self)@.set_tolerations(tolerations@.map_values(|toleration: Toleration| toleration@)),
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
            Some(t) => {
                self.inner.tolerations = Some(t.into_iter().map(|toleration: Toleration| toleration.into_kube()).collect())
            },
            None => {
                self.inner.tolerations = None
            }
        }
    }

    #[verifier(external_body)]
    pub fn set_node_selector(&mut self, node_selector: StringMap)
        ensures
            self@ == old(self)@.set_node_selector(node_selector@),
    {
        self.inner.node_selector = Some(node_selector.into_rust_map())
    }

    #[verifier(external_body)]
    pub fn overwrite_runtime_class_name(&mut self, runtime_class_name: Option<String>)
        ensures
            self@ == old(self)@.overwrite_runtime_class_name(opt_string_to_view(&runtime_class_name)),
    {
        match runtime_class_name {
            Some(n) => self.inner.runtime_class_name = Some(n.into_rust_string()),
            None => self.inner.runtime_class_name = None,
        }
        
    }

    #[verifier(external_body)]
    pub fn overwrite_dns_policy(&mut self, dns_policy: Option<String>)
        ensures
            self@ == old(self)@.overwrite_dns_policy(opt_string_to_view(&dns_policy)),
    {
        match dns_policy {
            Some(n) => self.inner.dns_policy = Some(n.into_rust_string()),
            None => self.inner.dns_policy = None,
        }
        
    }

    #[verifier(external_body)]
    pub fn overwrite_scheduler_name(&mut self, scheduler_name: Option<String>)
        ensures
            self@ == old(self)@.overwrite_scheduler_name(opt_string_to_view(&scheduler_name)),
    {
        match scheduler_name {
            Some(n) => self.inner.scheduler_name = Some(n.into_rust_string()),
            None => self.inner.scheduler_name = None,
        }
    }

    #[verifier(external_body)]
    pub fn overwrite_priority_class_name(&mut self, priority_class_name: Option<String>)
        ensures
            self@ == old(self)@.overwrite_priority_class_name(opt_string_to_view(&priority_class_name)),
    {
        match priority_class_name {
            Some(n) => self.inner.priority_class_name = Some(n.into_rust_string()),
            None => self.inner.priority_class_name = None,
        }
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::PodSpec) -> PodSpec {
        PodSpec { inner: inner }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::PodSpec {
        self.inner
    }
}

/// PodView is the ghost type of Pod.
/// It is supposed to be used in spec and proof code.

pub struct PodView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PodSpecView>,
    pub status: Option<PodStatusView>,
}

pub type PodStatusView = EmptyStatusView;

impl PodView {
    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> PodView {
        PodView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: PodSpecView) -> PodView {
        PodView {
            spec: Some(spec),
            ..self
        }
    }
}

impl ResourceView for PodView {
    type Spec = Option<PodSpecView>;
    type Status = Option<PodStatusView>;

    open spec fn default() -> PodView {
        PodView {
            metadata: ObjectMetaView::default(),
            spec: None,
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::PodKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<PodSpecView> {
        self.spec
    }

    open spec fn status(self) -> Option<PodStatusView> {
        self.status
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: PodView::marshal_spec(self.spec),
            status: PodView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<PodView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !PodView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !PodView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(PodView {
                metadata: obj.metadata,
                spec: PodView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: PodView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        PodView::marshal_spec_preserves_integrity();
        PodView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: Option<PodSpecView>) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<Option<PodSpecView>, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<PodStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<PodStatusView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity(){}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        &&& self.spec.is_Some()
    }

    open spec fn transition_validation(self, old_obj: PodView) -> bool {
        true
    }
}

pub struct PodSpecView {
    pub affinity: Option<AffinityView>,
    pub containers: Seq<ContainerView>,
    pub volumes: Option<Seq<VolumeView>>,
    pub init_containers: Option<Seq<ContainerView>>,
    pub service_account_name: Option<StringView>,
    pub tolerations: Option<Seq<TolerationView>>,
    pub node_selector: Option<Map<StringView, StringView>>,
    pub runtime_class_name: Option<StringView>,
    pub dns_policy: Option<StringView>,
    pub priority_class_name: Option<StringView>,
    pub scheduler_name: Option<StringView>,
}

impl PodSpecView {
    pub open spec fn default() -> PodSpecView {
        PodSpecView {
            affinity: None,
            containers: Seq::empty(),
            volumes: None,
            init_containers: None,
            service_account_name: None,
            tolerations: None,
            node_selector: None,
            runtime_class_name: None,
            dns_policy: None,
            priority_class_name: None,
            scheduler_name: None,
        }
    }

    pub open spec fn set_affinity(self, affinity: AffinityView) -> PodSpecView {
        PodSpecView {
            affinity: Some(affinity),
            ..self
        }
    }

    pub open spec fn unset_affinity(self) -> PodSpecView {
        PodSpecView {
            affinity: None,
            ..self
        }
    }

    pub open spec fn set_containers(self, containers: Seq<ContainerView>) -> PodSpecView {
        PodSpecView {
            containers: containers,
            ..self
        }
    }

    pub open spec fn set_volumes(self, volumes: Seq<VolumeView>) -> PodSpecView {
        PodSpecView {
            volumes: Some(volumes),
            ..self
        }
    }

    pub open spec fn set_init_containers(self, init_containers: Seq<ContainerView>) -> PodSpecView {
        PodSpecView {
            init_containers: Some(init_containers),
            ..self
        }
    }

    pub open spec fn set_service_account_name(self, service_account_name: StringView) -> PodSpecView {
        PodSpecView {
            service_account_name: Some(service_account_name),
            ..self
        }
    }

    pub open spec fn set_tolerations(self, tolerations: Seq<TolerationView>) -> PodSpecView {
        PodSpecView {
            tolerations: Some(tolerations),
            ..self
        }
    }

    pub open spec fn unset_tolerations(self) -> PodSpecView {
        PodSpecView {
            tolerations: None,
            ..self
        }
    }

    pub open spec fn set_node_selector(self, node_selector: Map<StringView, StringView>) -> PodSpecView {
        PodSpecView {
            node_selector: Some(node_selector),
            ..self
        }
    }

    pub open spec fn overwrite_runtime_class_name(self, runtime_class_name: Option<StringView>) -> PodSpecView {
        PodSpecView {
            runtime_class_name: runtime_class_name,
            ..self
        }
    }

    pub open spec fn overwrite_dns_policy(self, dns_policy: Option<StringView>) -> PodSpecView {
        PodSpecView {
            dns_policy: dns_policy,
            ..self
        }
    }

    pub open spec fn overwrite_scheduler_name(self, scheduler_name: Option<StringView>) -> PodSpecView {
        PodSpecView {
            scheduler_name: scheduler_name,
            ..self
        }
    }

    pub open spec fn overwrite_priority_class_name(self, priority_class_name: Option<StringView>) -> PodSpecView {
        PodSpecView {
            priority_class_name: priority_class_name,
            ..self
        }
    }
}

}
