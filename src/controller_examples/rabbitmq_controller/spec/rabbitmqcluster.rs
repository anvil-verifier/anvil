// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, marshal::*, object_meta::*, owner_reference::*,
    resource::*,
};
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {
pub struct RabbitmqClusterView {
    pub metadata: ObjectMetaView,
    pub spec: RabbitmqClusterSpecView,
}

impl RabbitmqClusterView {
    pub open spec fn well_formed(self) -> bool {
        &&& self.metadata.name.is_Some()
        &&& self.metadata.namespace.is_Some()
        &&& self.metadata.uid.is_Some()
    }

    // TODO: remove the redundant spec methods name() and namespace()
    pub open spec fn name(self) -> Option<StringView> {
        self.metadata.name
    }

    pub open spec fn namespace(self) -> Option<StringView> {
        self.metadata.namespace
    }

    pub open spec fn controller_owner_ref(self) -> OwnerReferenceView {
        OwnerReferenceView {
            block_owner_deletion: None,
            controller: Some(true),
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            uid: self.metadata.uid.get_Some_0(),
        }
    }
}

impl ResourceView for RabbitmqClusterView {
    type Spec = RabbitmqClusterSpecView;

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

    open spec fn spec(self) -> RabbitmqClusterSpecView {
        self.spec
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: RabbitmqClusterView::marshal_spec(self.spec)
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<RabbitmqClusterView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !RabbitmqClusterView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(RabbitmqClusterView {
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

    closed spec fn marshal_spec(s: RabbitmqClusterSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<RabbitmqClusterSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn spec_integrity_is_preserved_by_marshal() {}

    proof fn from_dynamic_object_result_determined_by_unmarshal() {}

    open spec fn rule(obj: RabbitmqClusterView) -> bool {
        true
    }

    open spec fn transition_rule(new_obj: RabbitmqClusterView, old_obj: RabbitmqClusterView) -> bool {
        new_obj.spec.replicas >= old_obj.spec.replicas
        && new_obj.spec.persistence == old_obj.spec.persistence
    }

}

pub struct RabbitmqClusterSpecView {
    pub replicas: int,
    pub persistence: RabbitmqClusterPersistenceSpecView,
    pub rabbitmq_config: Option<RabbitmqConfigView>,
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

pub struct RabbitmqConfigView {
    pub additional_config: Option<StringView>,
    pub advanced_config: Option<StringView>,
    pub env_config: Option<StringView>,
}

pub struct RabbitmqClusterPersistenceSpecView {
    pub storage_class_name: StringView,
    pub storage: StringView,
}


}
