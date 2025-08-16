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

    #[verifier(inline)]
    pub open spec fn _default() -> ConfigMapView {
        ConfigMapView {
            metadata: ObjectMetaView::default(),
            data: None,
        }
    }

    #[verifier(inline)]
    pub open spec fn _spec(self) -> ConfigMapSpecView {
        self.data
    }

    #[verifier(inline)]
    pub open spec fn _status(self) -> EmptyStatusView {
        empty_status()
    }

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> ConfigMapView {
        ConfigMapView {
            metadata: obj.metadata,
            data: ConfigMapView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool { true }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: ConfigMapView) -> bool { true }
}

implement_resource_view_trait!(ConfigMapView, ConfigMapSpecView, EmptyStatusView, _default, Kind::ConfigMapKind, _spec,
    _status, _unmarshal_helper, _state_validation, _transition_validation);

}
