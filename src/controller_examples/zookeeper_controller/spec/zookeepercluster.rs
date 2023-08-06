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
}

impl ResourceView for ZookeeperClusterView {
    type Spec = ZookeeperClusterSpecView;

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

    open spec fn spec(self) -> ZookeeperClusterSpecView {
        self.spec
    }

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

    closed spec fn marshal_spec(s: ZookeeperClusterSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<ZookeeperClusterSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn spec_integrity_is_preserved_by_marshal() {}

    open spec fn rule(obj: ZookeeperClusterView) -> bool {
        true
    }

    open spec fn transition_rule(new_obj: ZookeeperClusterView, old_obj: ZookeeperClusterView) -> bool {
        true
    }
}

pub struct ZookeeperClusterSpecView {
    pub replicas: int,
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
