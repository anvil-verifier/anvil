use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    label_selector::*, pod_template_spec::*, prelude::*,
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct VStatefulSetView {
    pub metadata: ObjectMetaView,
    pub spec: VStatefulSetSpecView,
    pub status: Option<VStatefulSetStatusView>,
}

pub type VStatefulSetStatusView = EmptyStatusView;

impl VStatefulSetView {
    pub open spec fn well_formed(self) -> bool {
        &&& self.metadata.well_formed()
        &&& self.state_validation()
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

impl ResourceView for VStatefulSetView {
    type Spec = VStatefulSetSpecView;
    type Status = Option<VStatefulSetStatusView>;

    open spec fn default() -> VStatefulSetView {
        VStatefulSetView {
            metadata: ObjectMetaView::default(),
            spec: arbitrary(), // TODO: specify default value for spec
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView { self.metadata }

    open spec fn kind() -> Kind { Kind::CustomResourceKind("vstatefulset"@) }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> VStatefulSetSpecView { self.spec }

    open spec fn status(self) -> Option<VStatefulSetStatusView> { self.status }

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
        } else if !VStatefulSetView::unmarshal_spec(obj.spec).is_Ok() {
            Err(())
        } else if !VStatefulSetView::unmarshal_status(obj.status).is_Ok() {
            Err(())
        } else {
            Ok(VStatefulSetView {
                metadata: obj.metadata,
                spec: VStatefulSetView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: VStatefulSetView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        VStatefulSetView::marshal_spec_preserves_integrity();
        VStatefulSetView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: VStatefulSetSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<VStatefulSetSpecView, UnmarshalError>;

    closed spec fn marshal_status(s: Option<VStatefulSetStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<VStatefulSetStatusView>, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        // selector exists, and its match_labels is not empty
        // TODO: revise it after supporting selector.match_expressions
        &&& self.spec.selector.match_labels.is_Some()
        &&& self.spec.selector.match_labels.get_Some_0().len() > 0
        // template and its metadata and spec exists
        &&& self.spec.template.is_Some()
        &&& self.spec.template.get_Some_0().metadata.is_Some()
        &&& self.spec.template.get_Some_0().spec.is_Some()
        // selector matches template's metadata's labels
        &&& self.spec.selector.matches(self.spec.template.get_Some_0().metadata.get_Some_0().labels.unwrap_or(Map::empty()))

        // replicas is non‑negative
        &&& self.spec.replicas.is_Some() ==>
        self.spec.replicas.get_Some_0() >= 0

        &&& self.spec.update_strategy.is_Some() ==> (
            // updateStrategy.type must be either RollingUpdate or OnDelete (used "type_" to avoid clashing with Rust keyword)
            self.spec.update_strategy.get_Some_0().type_.is_Some() ==> (
                (
                    self.spec.update_strategy.get_Some_0().type_.get_Some_0() == "OnDelete"@
                    && self.spec.update_strategy.get_Some_0().rolling_update.is_None()
                )
                ||
                (
                    self.spec.update_strategy.get_Some_0().type_.get_Some_0() == "RollingUpdate"@
                    && self.spec.update_strategy.get_Some_0().rolling_update.is_Some() ==>
                    (
                        // updateStrategy.rollingUpdate.partition is non-negative
                        self.spec.update_strategy.get_Some_0().rolling_update.get_Some_0().partition.is_Some() ==>
                        self.spec.update_strategy.get_Some_0().rolling_update.get_Some_0().partition.get_Some_0() >= 0
                        // if updateStrategy.rollingUpdate.maxUnavailable is present, validate it's positive (assuming its an integer for now)
                        && self.spec.update_strategy.get_Some_0().rolling_update.get_Some_0().max_unavailable.is_Some() ==>
                        self.spec.update_strategy.get_Some_0().rolling_update.get_Some_0().max_unavailable.get_Some_0() > 0
                    )
                )
            )
        )

        // podManagementPolicy must be either OrderedReady or Parallel
        &&& self.spec.pod_management_policy.is_Some() ==> (
            self.spec.pod_management_policy.get_Some_0() == "OrderedReady"@
            || self.spec.pod_management_policy.get_Some_0() == "Parallel"@
        )

        // volumeClaimTemplates
        // TODO: this object is too big, assume state_validation() is implemented for PersistentVolumeClaimSpec for now
        &&& self.spec.volume_claim_templates.is_Some() ==> (
            forall | i: int | #![auto] 0 <= i < self.spec.volume_claim_templates.get_Some_0().len() ==> self.spec.volume_claim_templates.get_Some_0()[i].state_validation()
        )

        // minReadySeconds must be non‑negative if present
        &&& self.spec.min_ready_seconds.is_Some() ==>
        self.spec.min_ready_seconds.get_Some_0() >= 0

        // persistentVolumeClaimRetentionPolicy.whenDeleted/whenScaled must be Delete or Retain
        &&& self.spec.persistent_volume_claim_retention_policy.is_Some() ==> (
            self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_deleted.is_Some() ==> (
                self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_deleted.get_Some_0() == "Retain"@
                || self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_deleted.get_Some_0() == "Delete"@
            )
            && self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_scaled.is_Some() ==>
            (
                self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_scaled.get_Some_0() == "Retain"@
                || self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_scaled.get_Some_0() == "Delete"@
            )
        )

        // ordinals.start must be non‑negative if ordinals is provided
        &&& self.spec.ordinals.is_Some() ==>
        self.spec.ordinals.get_Some_0().start >= 0
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

pub struct StatefulSetStrategyView {
    pub type_: Option<StringView>,
    pub rolling_update: Option<RollingUpdateStatefulSetView>,
}

pub struct RollingUpdateStatefulSetView {
    pub partition: Option<int>,
    pub max_unavailable: Option<int>,
}

pub struct StatefulSetPersistentVolumeClaimRetentionPolicyView {
    pub when_deleted: Option<StringView>,
    pub when_scaled: Option<StringView>,
}

pub struct StatefulSetOrdinalsView {
    pub start: int,
}

pub struct VStatefulSetSpecView {
    pub service_name: StringView,
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub template: Option<PodTemplateSpecView>,
    pub update_strategy: Option<StatefulSetStrategyView>,
    pub pod_management_policy: Option<StringView>,
    pub revision_history_limit: Option<int>,
    pub volume_claim_templates: Option<Seq<PersistentVolumeClaimView>>,
    pub min_ready_seconds: Option<int>,
    pub persistent_volume_claim_retention_policy: Option<StatefulSetPersistentVolumeClaimRetentionPolicyView>,
    pub ordinals: Option<StatefulSetOrdinalsView>,
}
}