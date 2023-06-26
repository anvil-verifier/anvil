// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*,
    object_meta::*, resource::*,
};
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct ZookeeperClusterView {
    pub metadata: ObjectMetaView,
    pub spec: ZookeeperClusterSpecView,
}

impl ZookeeperClusterView {
    pub open spec fn well_formed(self) -> bool {
        &&& self.metadata.name.is_Some()
        &&& self.metadata.namespace.is_Some()
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

    proof fn object_ref_is_well_formed() {}

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ZookeeperClusterView::marshal_spec(self.spec),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<ZookeeperClusterView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ZookeeperClusterView::unmarshal_spec(obj.spec).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(ZookeeperClusterView {
                metadata: obj.metadata,
                spec: ZookeeperClusterView::unmarshal_spec(obj.spec).get_Ok_0(),
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        ZookeeperClusterView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}
}

pub struct ZookeeperClusterSpecView {
    pub replica: int,
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
