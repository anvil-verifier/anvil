// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, marshal::*, object_meta::*, resource::*,
};
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct RabbitmqCluster {
    inner: deps_hack::RabbitmqCluster
}

pub struct RabbitmqClusterView {
    pub metadata: ObjectMetaView,
    pub spec: RabbitmqClusterSpecView,
}

impl RabbitmqCluster {
    pub spec fn view(&self) -> RabbitmqClusterView;

    #[verifier(external_body)]
    pub fn name(&self) -> (name: Option<String>)
        ensures
            self@.name().is_Some() == name.is_Some(),
            name.is_Some() ==> name.get_Some_0()@ == self@.name().get_Some_0(),
    {
        match &self.inner.metadata.name {
            std::option::Option::Some(n) => Option::Some(String::from_rust_string(n.to_string())),
            std::option::Option::None => Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn namespace(&self) -> (namespace: Option<String>)
        ensures
            self@.namespace().is_Some() == namespace.is_Some(),
            namespace.is_Some() ==> namespace.get_Some_0()@ == self@.namespace().get_Some_0(),
    {
        match &self.inner.metadata.namespace {
            std::option::Option::Some(n) => Option::Some(String::from_rust_string(n.to_string())),
            std::option::Option::None => Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn replica(&self) -> (replica: i32)
        ensures
            replica as int == self@.spec.replica,
    {
        self.inner.spec.replica
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::RabbitmqCluster {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == RabbitmqClusterView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::RabbitmqCluster>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<RabbitmqCluster, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == RabbitmqClusterView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == RabbitmqClusterView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::RabbitmqCluster>();
        if parse_result.is_ok() {
            let res = RabbitmqCluster { inner: parse_result.unwrap() };
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::RabbitmqCluster> for RabbitmqCluster {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::RabbitmqCluster) -> RabbitmqCluster {
        RabbitmqCluster {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::RabbitmqCluster {
        self.inner
    }
}

impl RabbitmqClusterView {
    pub open spec fn name(self) -> Option<StringView> {
        self.metadata.name
    }

    pub open spec fn namespace(self) -> Option<StringView> {
        self.metadata.namespace
    }

    pub closed spec fn marshal_spec(s: RabbitmqClusterSpecView) -> Value;

    pub closed spec fn unmarshal_spec(v: Value) -> Result<RabbitmqClusterSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    pub proof fn spec_integrity_is_preserved_by_marshal()
        ensures
            forall |s: RabbitmqClusterSpecView|
                Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)).is_Ok()
                && s == Self::unmarshal_spec(Self::marshal_spec(s)).get_Ok_0() {}
}

impl ResourceView for RabbitmqClusterView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::CustomResourceKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: RabbitmqClusterView::marshal_spec(self.spec)
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<RabbitmqClusterView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else if !RabbitmqClusterView::unmarshal_spec(obj.spec).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(RabbitmqClusterView {
                metadata: obj.metadata,
                spec: RabbitmqClusterView::unmarshal_spec(obj.spec).get_Ok_0(),
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        RabbitmqClusterView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}
}

#[verifier(external_body)]
pub struct RabbitmqClusterSpec {
    inner: deps_hack::RabbitmqClusterSpec,
}

pub struct RabbitmqClusterSpecView {
    pub replica: int,
}

impl RabbitmqClusterSpec {
    pub spec fn view(&self) -> RabbitmqClusterSpecView;

    #[verifier(external_body)]
    pub fn replica(&self) -> (replica: i32)
        ensures
            replica as int == self@.replica,
    {
        self.inner.replica
    }
}

impl RabbitmqClusterSpecView {}

impl Marshalable for RabbitmqClusterSpecView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}


}
