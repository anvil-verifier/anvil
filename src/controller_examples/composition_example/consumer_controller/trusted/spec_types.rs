// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::consumer_controller::trusted::step::*;
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{api_resource::*, prelude::*};
use crate::kubernetes_cluster::spec::{cluster::*, cluster_state_machine::*, message::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub type VRSStep = Step<VRSMessage>;

pub type VRSCluster = Cluster<ConsumerView, EmptyAPI, ConsumerReconciler>;

pub type VRSMessage = Message<EmptyTypeView, EmptyTypeView>;

pub struct ConsumerReconciler {}

pub struct ConsumerReconcileState {
    pub reconcile_step: ConsumerReconcileStepView,
}

pub struct ConsumerView {
    pub metadata: ObjectMetaView,
    pub spec: ConsumerSpecView,
    pub status: Option<ConsumerStatusView>,
}

pub type ConsumerStatusView = EmptyStatusView;

impl ConsumerView {
    pub open spec fn well_formed(self) -> bool {
        &&& self.metadata.name.is_Some()
        &&& self.metadata.namespace.is_Some()
        &&& self.metadata.uid.is_Some()
    }

    pub open spec fn controller_owner_ref(self) -> OwnerReferenceView {
        OwnerReferenceView {
            block_owner_deletion: Some(true),
            controller: Some(true),
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            uid: self.metadata.uid.get_Some_0(),
        }
    }
}

impl ResourceView for ConsumerView {
    type Spec = ConsumerSpecView;
    type Status = Option<ConsumerStatusView>;

    open spec fn default() -> ConsumerView {
        ConsumerView {
            metadata: ObjectMetaView::default(),
            spec: arbitrary(), // TODO: specify the default value for spec
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView { self.metadata }

    open spec fn kind() -> Kind { Kind::CustomResourceKind }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> ConsumerSpecView { self.spec }

    open spec fn status(self) -> Option<ConsumerStatusView> { self.status }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ConsumerView::marshal_spec(self.spec),
            status: ConsumerView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<ConsumerView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ConsumerView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ConsumerView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(ConsumerView {
                metadata: obj.metadata,
                spec: ConsumerView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: ConsumerView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        ConsumerView::marshal_spec_preserves_integrity();
        ConsumerView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: ConsumerSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<ConsumerSpecView, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<ConsumerStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<ConsumerStatusView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        true
    }

    open spec fn transition_validation(self, old_obj: ConsumerView) -> bool {
        true
    }

}

impl CustomResourceView for ConsumerView {
    proof fn kind_is_custom_resource() {}
}

pub struct ConsumerSpecView {
    pub message: StringView,
}

}
