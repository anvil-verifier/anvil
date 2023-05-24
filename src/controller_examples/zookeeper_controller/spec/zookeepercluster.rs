// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, marshal::*, object_meta::*, resource::*,
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

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::ZookeeperCluster {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::CustomResourceKind,
    {
        ApiResource::from_kube(kube::api::ApiResource::erase::<deps_hack::ZookeeperCluster>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(
            k8s_openapi::serde_json::from_str(&k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )

        // DynamicObject::from_kube(kube::api::DynamicObject {
        //     types: std::option::Option::Some(kube::api::TypeMeta {
        //         api_version: Self::api_resource().into_kube().api_version,
        //         kind: Self::api_resource().into_kube().kind,
        //     }),
        //     metadata: self.inner.metadata,
        //     data: k8s_openapi::serde_json::to_value(self.inner.spec).unwrap(),
        // })
    }

    /// Convert a DynamicObject to a ConfigMap
    // NOTE: This function assumes try_parse won't fail!
    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (zk: ZookeeperCluster)
        ensures
            zk@ == ZookeeperClusterView::from_dynamic_object(obj@),
    {
        ZookeeperCluster { inner: obj.into_kube().try_parse::<deps_hack::ZookeeperCluster>().unwrap() }
    }
}

impl ZookeeperClusterView {
    pub open spec fn name(self) -> Option<StringView> {
        self.metadata.name
    }

    pub open spec fn namespace(self) -> Option<StringView> {
        self.metadata.namespace
    }
}

impl ResourceView for ZookeeperClusterView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::CustomResourceKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: self.kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: self.kind(),
            metadata: self.metadata,
            data: Value::Object(Map::empty()
                                    .insert(spec_field(),
                                        Value::Object(Map::empty()
                                            .insert(spec_replica_field(), Value::Int(self.spec.replica)))
                                    )
                                ),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> ZookeeperClusterView {
        ZookeeperClusterView {
            metadata: obj.metadata,
            spec: ZookeeperClusterSpecView {
                replica: obj.data.get_Object_0()[spec_field()].get_Object_0()[spec_replica_field()].get_Int_0(),
            },
        }
    }

    proof fn to_dynamic_preserves_integrity() {}
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

pub open spec fn spec_field() -> nat {0}

pub open spec fn status_field() -> nat {1}

pub open spec fn spec_replica_field() -> nat {0}

}
