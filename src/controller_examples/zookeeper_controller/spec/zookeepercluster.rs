// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, object_meta::*, resource::*,
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
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::CustomResourceKind,
    {
        ApiResource::from_kube_api_resource(kube::api::ApiResource::erase::<deps_hack::ZookeeperCluster>(&()))
    }

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
            replica as nat == self@.spec.replica,
    {
        self.inner.spec.replica
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
                                            .insert(spec_replica_field(), Value::Nat(self.spec.replica)))
                                    )
                                ),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> ZookeeperClusterView {
        ZookeeperClusterView {
            metadata: obj.metadata,
            spec: ZookeeperClusterSpecView {
                replica: obj.data.get_Object_0()[spec_field()].get_Object_0()[spec_replica_field()].get_Nat_0(),
            },
        }
    }

    proof fn integrity_check() {}
}

#[verifier(external_body)]
pub struct ZookeeperClusterSpec {
    inner: deps_hack::ZookeeperClusterSpec,
}

pub struct ZookeeperClusterSpecView {
    pub replica: nat,
}

impl ZookeeperClusterSpec {
    pub spec fn view(&self) -> ZookeeperClusterSpecView;

    #[verifier(external_body)]
    pub fn replica(&self) -> (replica: i32)
        ensures
            replica as nat == self@.replica,
    {
        self.inner.replica
    }
}

impl ZookeeperClusterSpecView {}

pub open spec fn spec_field() -> nat {0}

pub open spec fn status_field() -> nat {1}

pub open spec fn spec_replica_field() -> nat {0}

}
