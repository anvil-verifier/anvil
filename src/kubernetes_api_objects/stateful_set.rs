// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::label_selector::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::persistent_volume_claim::*;
use crate::kubernetes_api_objects::pod_template_spec::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

/// StatefulSet is a type of API object used for managing stateful applications,
/// mainly a group of Pods and PersistentVolumeClaims attached to the Pods.
/// A StatefulSet object allows different types of Volumes attached to the pods,
/// including ConfigMaps, Secrets and PersistentVolumeClaims.
/// It also exposes the applications using a headless service.
///
/// This definition is a wrapper of StatefulSet defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/apps/v1/stateful_set.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/workloads/controllers/statefulset/.

#[verifier(external_body)]
pub struct StatefulSet {
    inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSet,
}

impl StatefulSet {
    pub spec fn view(&self) -> StatefulSetView;

    #[verifier(external_body)]
    pub fn default() -> (stateful_set: StatefulSet)
        ensures
            stateful_set@ == StatefulSetView::default(),
    {
        StatefulSet {
            inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSet::default(),
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
    pub fn spec(&self) -> (spec: Option<StatefulSetSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        if self.inner.spec.is_none() {
            Option::None
        } else {
            Option::Some(StatefulSetSpec::from_kube(self.inner.spec.as_ref().unwrap().clone()))
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
    pub fn set_spec(&mut self, spec: StatefulSetSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = std::option::Option::Some(spec.into_kube());
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == StatefulSetView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::apps::v1::StatefulSet>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    /// Convert a DynamicObject to a StatefulSet
    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<StatefulSet, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == StatefulSetView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == StatefulSetView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::apps::v1::StatefulSet>();
        if parse_result.is_ok() {
            let res = StatefulSet { inner: parse_result.unwrap() };
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::k8s_openapi::api::apps::v1::StatefulSet> for StatefulSet {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSet) -> StatefulSet {
        StatefulSet { inner: inner }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::api::apps::v1::StatefulSet {
        self.inner
    }
}

#[verifier(external_body)]
pub struct StatefulSetSpec {
    inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec,
}

impl StatefulSetSpec {
    pub spec fn view(&self) -> StatefulSetSpecView;

    #[verifier(external_body)]
    pub fn default() -> (stateful_set_spec: StatefulSetSpec)
        ensures
            stateful_set_spec@ == StatefulSetSpecView::default(),
    {
        StatefulSetSpec {
            inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_replicas(&mut self, replicas: i32)
        ensures
            self@ == old(self)@.set_replicas(replicas as int),
    {
        self.inner.replicas = std::option::Option::Some(replicas)
    }

    #[verifier(external_body)]
    pub fn set_selector(&mut self, selector: LabelSelector)
        ensures
            self@ == old(self)@.set_selector(selector@),
    {
        self.inner.selector = selector.into_kube()
    }

    #[verifier(external_body)]
    pub fn set_service_name(&mut self, service_name: String)
        ensures
            self@ == old(self)@.set_service_name(service_name@),
    {
        self.inner.service_name = service_name.into_rust_string()
    }

    #[verifier(external_body)]
    pub fn set_template(&mut self, template: PodTemplateSpec)
        ensures
            self@ == old(self)@.set_template(template@),
    {
        self.inner.template = template.into_kube()
    }

    #[verifier(external_body)]
    pub fn set_volume_claim_templates(&mut self, volume_claim_templates: Vec<PersistentVolumeClaim>)
        ensures
            self@ == old(self)@.set_volume_claim_templates(volume_claim_templates@.map_values(|pvc: PersistentVolumeClaim| pvc@)),
    {
        self.inner.volume_claim_templates = std::option::Option::Some(
            volume_claim_templates.into_iter().map(|pvc: PersistentVolumeClaim| pvc.into_kube()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_pod_management_policy(&mut self, pod_management_policy: String)
        ensures
            self@ == old(self)@.set_pod_management_policy(pod_management_policy@),
    {
        self.inner.pod_management_policy = std::option::Option::Some(pod_management_policy.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn set_pvc_retention_policy(&mut self, pvc_retention_policy: StatefulSetPersistentVolumeClaimRetentionPolicy)
        ensures
            self@ == old(self)@.set_pvc_retention_policy(pvc_retention_policy@),
    {
        self.inner.persistent_volume_claim_retention_policy = std::option::Option::Some(pvc_retention_policy.into_kube())
    }

    #[verifier(external_body)]
    pub fn replicas(&self) -> (replicas: Option<i32>)
        ensures
            self@.replicas.is_Some() == replicas.is_Some(),
            replicas.is_Some() ==> replicas.get_Some_0() == self@.replicas.get_Some_0(),
    {
        if self.inner.replicas.is_none() {
            Option::None
        } else {
            Option::Some(self.inner.replicas.clone().unwrap())
        }
    }

}

impl ResourceWrapper<deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec> for StatefulSetSpec {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec) -> StatefulSetSpec {
        StatefulSetSpec { inner: inner }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::api::apps::v1::StatefulSetSpec {
        self.inner
    }
}

/// StatefulSetView is the ghost type of StatefulSet.
/// It is supposed to be used in spec and proof code.

pub struct StatefulSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<StatefulSetSpecView>,
}

impl StatefulSetView {
    pub open spec fn default() -> StatefulSetView {
        StatefulSetView {
            metadata: ObjectMetaView::default(),
            spec: Option::None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> StatefulSetView {
        StatefulSetView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: StatefulSetSpecView) -> StatefulSetView {
        StatefulSetView {
            spec: Option::Some(spec),
            ..self
        }
    }

    pub closed spec fn marshal_spec(s: Option<StatefulSetSpecView>) -> Value;

    pub closed spec fn unmarshal_spec(v: Value) -> Result<Option<StatefulSetSpecView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    pub proof fn spec_integrity_is_preserved_by_marshal()
        ensures
            forall |s: Option<StatefulSetSpecView>|
                Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)).is_Ok()
                && s == Self::unmarshal_spec(Self::marshal_spec(s)).get_Ok_0() {}
}

impl ResourceView for StatefulSetView {
    type Spec = Option<StatefulSetSpecView>;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::StatefulSetKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<StatefulSetSpecView> {
        self.spec
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: StatefulSetView::marshal_spec(self.spec),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<StatefulSetView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else if !StatefulSetView::unmarshal_spec(obj.spec).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(StatefulSetView {
                metadata: obj.metadata,
                spec: StatefulSetView::unmarshal_spec(obj.spec).get_Ok_0(),
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        StatefulSetView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}
}

pub struct StatefulSetSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub service_name: StringView,
    pub template: PodTemplateSpecView,
    pub volume_claim_templates: Option<Seq<PersistentVolumeClaimView>>,
    pub pod_management_policy: Option<StringView>,
    pub persistent_volume_claim_retention_policy: Option<StatefulSetPersistentVolumeClaimRetentionPolicyView>,
}

impl StatefulSetSpecView {
    pub open spec fn default() -> StatefulSetSpecView {
        StatefulSetSpecView {
            replicas: Option::None,
            selector: LabelSelectorView::default(),
            service_name: new_strlit("")@,
            template: PodTemplateSpecView::default(),
            volume_claim_templates: Option::None,
            pod_management_policy: Option::None,
            persistent_volume_claim_retention_policy: Option::None,
        }
    }

    pub open spec fn set_replicas(self, replicas: int) -> StatefulSetSpecView {
        StatefulSetSpecView {
            replicas: Option::Some(replicas),
            ..self
        }
    }

    pub open spec fn set_selector(self, selector: LabelSelectorView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            selector: selector,
            ..self
        }
    }

    pub open spec fn set_service_name(self, service_name: StringView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            service_name: service_name,
            ..self
        }
    }

    pub open spec fn set_template(self, template: PodTemplateSpecView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            template: template,
            ..self
        }
    }

    pub open spec fn set_volume_claim_templates(self, volume_claim_templates: Seq<PersistentVolumeClaimView>) -> StatefulSetSpecView {
        StatefulSetSpecView {
            volume_claim_templates: Option::Some(volume_claim_templates),
            ..self
        }
    }

    pub open spec fn set_pod_management_policy(self, pod_management_policy: StringView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            pod_management_policy: Option::Some(pod_management_policy),
            ..self
        }
    }

    pub open spec fn set_pvc_retention_policy(self, pvc_retention_policy: StatefulSetPersistentVolumeClaimRetentionPolicyView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            persistent_volume_claim_retention_policy: Option::Some(pvc_retention_policy),
            ..self
        }
    }
}

impl Marshalable for StatefulSetSpecView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
