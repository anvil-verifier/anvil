// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*,
    object_meta::*, resource::*,
};
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct ZookeeperCluster {
    inner: deps_hack::ZookeeperCluster
}

pub struct ZookeeperClusterView {
    pub metadata: ObjectMetaView,
    pub spec: ZookeeperClusterSpecView,
}

impl ZookeeperCluster {
    pub spec fn view(&self) -> ZookeeperClusterView;

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

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == ZookeeperClusterView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::ZookeeperCluster>(&()))
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
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<ZookeeperCluster, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ZookeeperClusterView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ZookeeperClusterView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::ZookeeperCluster>();
        if parse_result.is_ok() {
            let res = ZookeeperCluster { inner: parse_result.unwrap() };
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::ZookeeperCluster> for ZookeeperCluster {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::ZookeeperCluster) -> ZookeeperCluster {
        ZookeeperCluster {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::ZookeeperCluster {
        self.inner
    }
}

impl ZookeeperClusterView {
    pub open spec fn name(self) -> Option<StringView> {
        self.metadata.name
    }

    pub open spec fn namespace(self) -> Option<StringView> {
        self.metadata.namespace
    }

    pub closed spec fn marshal_spec(s: ZookeeperClusterSpecView) -> Value;

    pub closed spec fn unmarshal_spec(v: Value) -> Result<ZookeeperClusterSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    pub proof fn spec_integrity_is_preserved_by_marshal()
        ensures
            forall |s: ZookeeperClusterSpecView|
                Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)).is_Ok()
                && s == Self::unmarshal_spec(Self::marshal_spec(s)).get_Ok_0() {}
}

impl ResourceView for ZookeeperClusterView {
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

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            data: ZookeeperClusterView::marshal_spec(self.spec),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<ZookeeperClusterView, ParseDynamicObjectError> {
        if !ZookeeperClusterView::unmarshal_spec(obj.data).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(ZookeeperClusterView {
                metadata: obj.metadata,
                spec: ZookeeperClusterView::unmarshal_spec(obj.data).get_Ok_0(),
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        ZookeeperClusterView::spec_integrity_is_preserved_by_marshal();
    }
}

#[verifier(external_body)]
pub struct ZookeeperClusterSpec {
    inner: deps_hack::ZookeeperClusterSpec,
}

pub struct ZookeeperClusterSpecView {
    pub replica: int,
}

impl ZookeeperClusterSpec {
    pub spec fn view(&self) -> ZookeeperClusterSpecView;

    #[verifier(external_body)]
    pub fn replica(&self) -> (replica: i32)
        ensures
            replica as int == self@.replica,
    {
        self.inner.replica
    }
}

impl ZookeeperClusterSpecView {}

impl Marshalable for ZookeeperClusterSpecView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
