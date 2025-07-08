// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*, object_meta::*, resource::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// ConfigMapView is the ghost type of ConfigMap.


pub struct ConfigMapView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>,
}

// This ConfigMapSpecView is defined only to call marshal_spec and unmarshal_spec conveniently
// Unlike most other Kubernetes objects, a ConfigMap does not have a spec field,
// but its data, binary_data and immutable fields are treated similarly as spec of other objects.
// Here we use a tuple to wrap around ConfigMap's fields (we will implement more fields like binary_data later)
// instead of defining another struct.
//
// We use a unit type in the tuple because there has to be at least two members in a tuple.
// The unit type will be replaced once we support other fields than data.
type ConfigMapSpecView = Option<Map<StringView, StringView>>;

impl ConfigMapView {
    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> ConfigMapView {
        ConfigMapView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_data(self, data: Map<StringView, StringView>) -> ConfigMapView {
        ConfigMapView {
            data: Some(data),
            ..self
        }
    }
}

impl ResourceView for ConfigMapView {
    type Spec = ConfigMapSpecView;
    type Status = EmptyStatusView;

    open spec fn default() -> ConfigMapView {
        ConfigMapView {
            metadata: ObjectMetaView::default(),
            data: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::ConfigMapKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> ConfigMapSpecView {
        self.data
    }

    open spec fn status(self) -> EmptyStatusView {
        empty_status()
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ConfigMapView::marshal_spec(self.data),
            status: ConfigMapView::marshal_status(empty_status()),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<ConfigMapView, UnmarshalError> {
        if obj.kind != Self::kind() {
            Err(())
        } else if !(ConfigMapView::unmarshal_spec(obj.spec) is Ok) {
            Err(())
        } else if !(ConfigMapView::unmarshal_status(obj.status) is Ok) {
            Err(())
        } else {
            Ok(ConfigMapView {
                metadata: obj.metadata,
                data: ConfigMapView::unmarshal_spec(obj.spec)->Ok_0,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        ConfigMapView::marshal_spec_preserves_integrity();
        ConfigMapView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    uninterp spec fn marshal_spec(s: ConfigMapSpecView) -> Value;

    uninterp spec fn unmarshal_spec(v: Value) -> Result<ConfigMapSpecView, UnmarshalError>;

    uninterp spec fn marshal_status(s: EmptyStatusView) -> Value;

    uninterp spec fn unmarshal_status(v: Value) -> Result<EmptyStatusView, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        true
    }

    open spec fn transition_validation(self, old_obj: ConfigMapView) -> bool {
        true
    }
}

}
