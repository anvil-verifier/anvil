// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
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
            res@.kind == Kind::CustomResourceKind,
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

    /// Convert a DynamicObject to a ConfigMap
    // NOTE: This function assumes try_parse won't fail!
    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (rabbitmq: RabbitmqCluster)
        ensures
            rabbitmq@ == RabbitmqClusterView::from_dynamic_object(obj@),
    {
        RabbitmqCluster { inner: obj.into_kube().try_parse::<deps_hack::RabbitmqCluster>().unwrap() }
    }
}

impl RabbitmqClusterView {
    pub open spec fn name(self) -> Option<StringView> {
        self.metadata.name
    }

    pub open spec fn namespace(self) -> Option<StringView> {
        self.metadata.namespace
    }
}

impl ResourceView for RabbitmqClusterView {
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

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> RabbitmqClusterView {
        RabbitmqClusterView {
            metadata: obj.metadata,
            spec: RabbitmqClusterSpecView {
                replica: obj.data.get_Object_0()[spec_field()].get_Object_0()[spec_replica_field()].get_Int_0(),
            },
        }
    }

    proof fn to_dynamic_preserves_integrity() {}
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

pub open spec fn spec_field() -> nat {0}

pub open spec fn status_field() -> nat {1}

pub open spec fn spec_replica_field() -> nat {0}

}
