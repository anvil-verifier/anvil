// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::fluent_controller::fluentbit_config::trusted::step::*;
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, object_meta::*, owner_reference::*, resource::*,
    resource_requirements::*,
};
use crate::kubernetes_cluster::spec::{cluster::*, cluster_state_machine::*, message::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub type FBCStep = Step<FBCMessage>;

pub type FBCCluster = Cluster<FluentBitConfigView, EmptyAPI, FluentBitConfigReconciler>;

pub type FBCMessage = Message<EmptyTypeView, EmptyTypeView>;

pub struct FluentBitConfigReconciler {}

pub struct FluentBitConfigReconcileState {
    pub reconcile_step: FluentBitConfigReconcileStep,
}

pub struct FluentBitConfigView {
    pub metadata: ObjectMetaView,
    pub spec: FluentBitConfigSpecView,
    pub status: Option<FluentBitConfigStatusView>,
}

pub type FluentBitConfigStatusView = EmptyStatusView;

impl FluentBitConfigView {
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

impl ResourceView for FluentBitConfigView {
    type Spec = FluentBitConfigSpecView;
    type Status = Option<FluentBitConfigStatusView>;

    open spec fn default() -> FluentBitConfigView {
        FluentBitConfigView {
            metadata: ObjectMetaView::default(),
            spec: arbitrary(), // TODO: specify the default value for spec
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView { self.metadata }

    open spec fn kind() -> Kind { Kind::CustomResourceKind("fluentbitconfig"@) }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> FluentBitConfigSpecView { self.spec }

    open spec fn status(self) -> Option<FluentBitConfigStatusView> { self.status }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: FluentBitConfigView::marshal_spec(self.spec),
            status: FluentBitConfigView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<FluentBitConfigView, UnmarshalError> {
        if obj.kind != Self::kind() {
            Err(())
        } else if !FluentBitConfigView::unmarshal_spec(obj.spec).is_Ok() {
            Err(())
        } else if !FluentBitConfigView::unmarshal_status(obj.status).is_Ok() {
            Err(())
        } else {
            Ok(FluentBitConfigView {
                metadata: obj.metadata,
                spec: FluentBitConfigView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: FluentBitConfigView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        FluentBitConfigView::marshal_spec_preserves_integrity();
        FluentBitConfigView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    uninterp spec fn marshal_spec(s: FluentBitConfigSpecView) -> Value;

    uninterp spec fn unmarshal_spec(v: Value) -> Result<FluentBitConfigSpecView, UnmarshalError>;

    uninterp spec fn marshal_status(s: Option<FluentBitConfigStatusView>) -> Value;

    uninterp spec fn unmarshal_status(v: Value) -> Result<Option<FluentBitConfigStatusView>, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool { true }

    open spec fn transition_validation(self, old_obj: FluentBitConfigView) -> bool { true }
}

impl CustomResourceView for FluentBitConfigView {
    proof fn kind_is_custom_resource() {}

    open spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool { true }

    proof fn validation_result_determined_by_spec_and_status()
        ensures forall |obj: Self| #[trigger] obj.state_validation() == Self::spec_status_validation(obj.spec(), obj.status())
    {}
}

pub struct FluentBitConfigSpecView {
    pub fluentbit_config: StringView,
    pub parsers_config: StringView,
}

}
