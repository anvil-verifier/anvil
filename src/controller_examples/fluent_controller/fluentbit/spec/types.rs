// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::fluent_controller::fluentbit::common::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::{
    affinity::*, api_resource::*, common::*, dynamic::*, marshal::*, object_meta::*,
    owner_reference::*, resource::*, resource_requirements::*, toleration::*,
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct FluentBitReconcileState {
    pub reconcile_step: FluentBitReconcileStep,
}

pub struct FluentBitView {
    pub metadata: ObjectMetaView,
    pub spec: FluentBitSpecView,
    pub status: Option<FluentBitStatusView>,
}

pub type FluentBitStatusView = EmptyStatusView;

impl FluentBitView {
    pub open spec fn well_formed(self) -> bool {
        &&& self.metadata.name.is_Some()
        &&& self.metadata.namespace.is_Some()
        &&& self.metadata.uid.is_Some()
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

impl ResourceView for FluentBitView {
    type Spec = FluentBitSpecView;
    type Status = Option<FluentBitStatusView>;

    open spec fn default() -> FluentBitView {
        FluentBitView {
            metadata: ObjectMetaView::default(),
            spec: arbitrary(), // TODO: specify the default value for spec
            status: None,
        }
    }

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

    open spec fn spec(self) -> FluentBitSpecView {
        self.spec
    }

    open spec fn status(self) -> Option<FluentBitStatusView> {
        self.status
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: FluentBitView::marshal_spec(self.spec),
            status: FluentBitView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<FluentBitView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !FluentBitView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !FluentBitView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(FluentBitView {
                metadata: obj.metadata,
                spec: FluentBitView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: FluentBitView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        FluentBitView::marshal_spec_preserves_integrity();
        FluentBitView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: FluentBitSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<FluentBitSpecView, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<FluentBitStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<FluentBitStatusView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        true
    }

    open spec fn transition_validation(self, old_obj: FluentBitView) -> bool {
        true
    }
}

pub struct FluentBitSpecView {
    pub fluentbit_config_name: StringView,
    pub image: StringView,
    pub resources: Option<ResourceRequirementsView>,
    pub tolerations: Option<Seq<TolerationView>>,
    pub labels: Map<StringView, StringView>,
    pub annotations: Map<StringView, StringView>,
    pub affinity: Option<AffinityView>,
    pub node_selector: Map<StringView, StringView>,
    pub runtime_class_name: StringView,
}

impl FluentBitSpecView {}

impl Marshalable for FluentBitSpecView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
