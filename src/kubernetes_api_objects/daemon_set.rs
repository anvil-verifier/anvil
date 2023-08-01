// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::label_selector::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::pod_template_spec::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

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
        ensures
            daemon_set@ == DaemonSetView::default(),
    {
        DaemonSet {
            inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSet::default(),
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
    pub fn spec(&self) -> (spec: Option<DaemonSetSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        if self.inner.spec.is_none() {
            Option::None
        } else {
            Option::Some(DaemonSetSpec::from_kube(self.inner.spec.as_ref().unwrap().clone()))
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
    pub fn set_spec(&mut self, spec: DaemonSetSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = std::option::Option::Some(spec.into_kube());
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == DaemonSetView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::apps::v1::DaemonSet>(&()))
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

    /// Convert a DynamicObject to a DaemonSet
    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<DaemonSet, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == DaemonSetView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == DaemonSetView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::apps::v1::DaemonSet>();
        if parse_result.is_ok() {
            let res = DaemonSet { inner: parse_result.unwrap() };
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::k8s_openapi::api::apps::v1::DaemonSet> for DaemonSet {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSet) -> DaemonSet {
        DaemonSet { inner: inner }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::api::apps::v1::DaemonSet {
        self.inner
    }
}

#[verifier(external_body)]
pub struct DaemonSetSpec {
    inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec,
}

impl DaemonSetSpec {
    pub spec fn view(&self) -> DaemonSetSpecView;

    #[verifier(external_body)]
    pub fn default() -> (daemon_set_spec: DaemonSetSpec)
        ensures
            daemon_set_spec@ == DaemonSetSpecView::default(),
    {
        DaemonSetSpec {
            inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_selector(&mut self, selector: LabelSelector)
        ensures
            self@ == old(self)@.set_selector(selector@),
    {
        self.inner.selector = selector.into_kube()
    }

    #[verifier(external_body)]
    pub fn set_template(&mut self, template: PodTemplateSpec)
        ensures
            self@ == old(self)@.set_template(template@),
    {
        self.inner.template = template.into_kube()
    }
}

impl ResourceWrapper<deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec> for DaemonSetSpec {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec) -> DaemonSetSpec {
        DaemonSetSpec { inner: inner }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::api::apps::v1::DaemonSetSpec {
        self.inner
    }
}

/// DaemonSetView is the ghost type of DaemonSet.
/// It is supposed to be used in spec and proof code.

pub struct DaemonSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<DaemonSetSpecView>,
}

impl DaemonSetView {
    pub open spec fn default() -> DaemonSetView {
        DaemonSetView {
            metadata: ObjectMetaView::default(),
            spec: Option::None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> DaemonSetView {
        DaemonSetView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: DaemonSetSpecView) -> DaemonSetView {
        DaemonSetView {
            spec: Option::Some(spec),
            ..self
        }
    }

    pub closed spec fn marshal_spec(s: Option<DaemonSetSpecView>) -> Value;

    pub closed spec fn unmarshal_spec(v: Value) -> Result<Option<DaemonSetSpecView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    pub proof fn spec_integrity_is_preserved_by_marshal()
        ensures
            forall |s: Option<DaemonSetSpecView>|
                Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)).is_Ok()
                && s == Self::unmarshal_spec(Self::marshal_spec(s)).get_Ok_0() {}
}

impl ResourceView for DaemonSetView {
    type Spec = Option<DaemonSetSpecView>;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::DaemonSetKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<DaemonSetSpecView> {
        self.spec
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: DaemonSetView::marshal_spec(self.spec),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<DaemonSetView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else if !DaemonSetView::unmarshal_spec(obj.spec).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(DaemonSetView {
                metadata: obj.metadata,
                spec: DaemonSetView::unmarshal_spec(obj.spec).get_Ok_0(),
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        DaemonSetView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}
}

pub struct DaemonSetSpecView {
    pub selector: LabelSelectorView,
    pub template: PodTemplateSpecView,
}

impl DaemonSetSpecView {
    pub open spec fn default() -> DaemonSetSpecView {
        DaemonSetSpecView {
            selector: LabelSelectorView::default(),
            template: PodTemplateSpecView::default(),
        }
    }

    pub open spec fn set_selector(self, selector: LabelSelectorView) -> DaemonSetSpecView {
        DaemonSetSpecView {
            selector: selector,
            ..self
        }
    }

    pub open spec fn set_template(self, template: PodTemplateSpecView) -> DaemonSetSpecView {
        DaemonSetSpecView {
            template: template,
            ..self
        }
    }
}

impl Marshalable for DaemonSetSpecView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}