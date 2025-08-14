use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{label_selector::*, pod_template_spec::*, prelude::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct VStatefulSetView {
    pub metadata: ObjectMetaView,
    pub spec: StatefulSetSpecView,
    pub status: Option<StatefulSetStatusView>,
}

impl VStatefulSetView {
    pub open spec fn well_formed(self) -> bool {
        &&& self.metadata.well_formed_for_namespaced()
        &&& self.state_validation()
    }

    pub open spec fn controller_owner_ref(self) -> OwnerReferenceView {
        OwnerReferenceView {
            block_owner_deletion: Some(true),
            controller: Some(true),
            kind: Self::kind(),
            name: self.metadata.name->0,
            uid: self.metadata.uid->0,
        }
    }

    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> VStatefulSetView {
        VStatefulSetView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_spec(self, spec: StatefulSetSpecView) -> VStatefulSetView {
        VStatefulSetView {
            spec: spec,
            ..self
        }
    }
}

impl ResourceView for VStatefulSetView {
    type Spec = StatefulSetSpecView;
    type Status = Option<StatefulSetStatusView>;

    open spec fn default() -> VStatefulSetView {
        VStatefulSetView {
            metadata: ObjectMetaView::default(),
            spec: StatefulSetSpecView::default(),
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView { self.metadata }

    open spec fn kind() -> Kind { Kind::CustomResourceKind("vstatefulset"@) }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> StatefulSetSpecView { self.spec }

    open spec fn status(self) -> Option<StatefulSetStatusView> { self.status }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: VStatefulSetView::marshal_spec(self.spec),
            status: VStatefulSetView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<VStatefulSetView, UnmarshalError> {
        if obj.kind != Self::kind() {
            Err(())
        } else if !(VStatefulSetView::unmarshal_spec(obj.spec) is Ok) {
            Err(())
        } else if !(VStatefulSetView::unmarshal_status(obj.status) is Ok) {
            Err(())
        } else {
            Ok(VStatefulSetView {
                metadata: obj.metadata,
                spec: VStatefulSetView::unmarshal_spec(obj.spec)->Ok_0,
                status: VStatefulSetView::unmarshal_status(obj.status)->Ok_0,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        VStatefulSetView::marshal_spec_preserves_integrity();
        VStatefulSetView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    uninterp spec fn marshal_spec(s: StatefulSetSpecView) -> Value;

    uninterp spec fn unmarshal_spec(v: Value) -> Result<StatefulSetSpecView, UnmarshalError>;

    uninterp spec fn marshal_status(s: Option<StatefulSetStatusView>) -> Value;

    uninterp spec fn unmarshal_status(v: Value) -> Result<Option<StatefulSetStatusView>, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        // selector exists, and its match_labels is not empty
        // TODO: revise it after supporting selector.match_expressions
        &&& self.spec.selector.match_labels is Some
        &&& self.spec.selector.match_labels->0.len() > 0
        // template and its metadata and spec exists
        &&& self.spec.template.metadata is Some
        &&& self.spec.template.spec is Some
        // selector matches template's metadata's labels
        &&& self.spec.selector.matches(self.spec.template.metadata->0.labels.unwrap_or(Map::empty()))

        // replicas is non‑negative
        &&& self.spec.replicas is Some ==>
        self.spec.replicas->0 >= 0

        &&& self.spec.update_strategy is Some ==> {
            (
                self.spec.update_strategy->0.type_ is Some ==> (
                    (
                        self.spec.update_strategy->0.type_->0 == "OnDelete"@
                        // rollingUpdate block only appear when type == "RollingUpdate"
                        && self.spec.update_strategy->0.rolling_update is None
                    )
                    || (
                        self.spec.update_strategy->0.type_->0 == "RollingUpdate"@
                        && (self.spec.update_strategy->0.rolling_update is Some ==>
                            // partition should be non-negative, maxUnavailable should be positive
                            match (self.spec.update_strategy->0.rolling_update->0.partition, self.spec.update_strategy->0.rolling_update->0.max_unavailable) {
                                (Some(partition), Some(max_unavailable)) => partition >= 0 && max_unavailable > 0,
                                (Some(partition), None) => partition >= 0,
                                (None, Some(max_unavailable)) => max_unavailable > 0,
                                (None, None) => true,
                            }
                        )
                    )
                )
            )
        }

        // podManagementPolicy must be either OrderedReady or Parallel
        &&& self.spec.pod_management_policy is Some ==> (
            self.spec.pod_management_policy->0 == "OrderedReady"@
            || self.spec.pod_management_policy->0 == "Parallel"@
        )

        // volumeClaimTemplates
        &&& self.spec.volume_claim_templates is Some ==> (
            forall | i: int | 0 <= i < self.spec.volume_claim_templates->0.len() ==> #[trigger] self.spec.volume_claim_templates->0[i].state_validation()
        )

        // minReadySeconds must be non‑negative if present
        &&& self.spec.min_ready_seconds is Some ==>
        self.spec.min_ready_seconds->0 >= 0

        // persistentVolumeClaimRetentionPolicy.whenDeleted/whenScaled must be Delete or Retain
        &&& self.spec.persistent_volume_claim_retention_policy is Some ==> (
            match (self.spec.persistent_volume_claim_retention_policy->0.when_deleted, self.spec.persistent_volume_claim_retention_policy->0.when_scaled) {
                (Some(when_deleted), Some(when_scaled)) => (when_deleted == "Retain"@ || when_deleted == "Delete"@) && (when_scaled == "Retain"@ || when_scaled == "Delete"@),
                (Some(when_deleted), None) => when_deleted == "Retain"@ || when_deleted == "Delete"@,
                (None, Some(when_scaled)) => when_scaled == "Retain"@ || when_scaled == "Delete"@,
                (None, None) => true,
            }
        )

        // ordinals.start must be non‑negative if ordinals is provided
        &&& self.spec.ordinals is Some ==> (
            self.spec.ordinals->0.start is Some ==>
                self.spec.ordinals->0.start->0 >= 0
        )
    }

    open spec fn transition_validation(self, old_obj: VStatefulSetView) -> bool {
        true
    }
}

impl CustomResourceView for VStatefulSetView {
    proof fn kind_is_custom_resource() {}

    open spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool {
        VStatefulSetView {
            metadata: arbitrary(),
            spec: obj_spec,
            status: obj_status,
        }.state_validation()
    }

    proof fn validation_result_determined_by_spec_and_status() {}
}

}
