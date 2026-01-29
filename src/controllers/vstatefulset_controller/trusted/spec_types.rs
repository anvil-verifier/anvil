use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{label_selector::*, pod_template_spec::*, persistent_volume_claim::*, prelude::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub spec const StatefulSetPodNameLabel: StringView = "statefulset.kubernetes.io/pod-name"@;
pub spec const StatefulSetOrdinalLabel: StringView = "apps.kubernetes.io/pod-index"@;

pub struct VStatefulSetView {
    pub metadata: ObjectMetaView,
    pub spec: VStatefulSetSpecView,
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

    pub open spec fn with_spec(self, spec: VStatefulSetSpecView) -> VStatefulSetView {
        VStatefulSetView {
            spec: spec,
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn _kind() -> Kind { Kind::CustomResourceKind("vstatefulset"@) }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        // selector exists, and its match_labels is not empty
        // TODO: revise it after supporting selector.match_expressions
        &&& self.spec.selector.match_labels is Some
        &&& self.spec.selector.match_labels->0.len() > 0
        // template and its metadata and spec exists
        &&& self.spec.template.metadata is Some
        &&& self.spec.template.spec is Some
        // selector matches template's metadata's labels
        &&& self.spec.selector.matches(self.spec.template.metadata->0.labels.unwrap_or(Map::empty()))
        &&& self.spec.template.metadata->0.labels is Some ==>
            (!self.spec.template.metadata->0.labels->0.contains_key(StatefulSetPodNameLabel) &&
            !self.spec.template.metadata->0.labels->0.contains_key(StatefulSetOrdinalLabel))

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
            forall | i: int | #![trigger self.spec.volume_claim_templates->0[i]] 0 <= i < self.spec.volume_claim_templates->0.len() ==> {
                let pvc_template = self.spec.volume_claim_templates->0[i];
                &&& pvc_template.state_validation() 
                &&& pvc_template.metadata.well_formed_for_namespaced()
                // fix https://github.com/kubernetes/kubernetes/issues/41153 
                &&& dash_free(pvc_template.metadata.name->0)
            }
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

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: VStatefulSetView) -> bool { true }
}

implement_resource_view_trait!(VStatefulSetView, VStatefulSetSpecView, VStatefulSetSpecView::default(),
    Option<StatefulSetStatusView>, None, VStatefulSetView::_kind(), _state_validation, _transition_validation);

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

pub struct VStatefulSetSpecView {
    pub service_name: StringView,
    pub selector: LabelSelectorView,
    pub template: PodTemplateSpecView,
    pub replicas: Option<int>,
    pub update_strategy: Option<StatefulSetUpdateStrategyView>,
    pub pod_management_policy: Option<StringView>,
    pub revision_history_limit: Option<int>,
    pub volume_claim_templates: Option<Seq<PersistentVolumeClaimView>>,
    pub min_ready_seconds: Option<int>,
    pub persistent_volume_claim_retention_policy: Option<StatefulSetPersistentVolumeClaimRetentionPolicyView>,
    pub ordinals: Option<StatefulSetOrdinalsView>,
}

impl VStatefulSetSpecView {
    pub open spec fn default() -> VStatefulSetSpecView {
        VStatefulSetSpecView {
            service_name: StringView::empty(),
            selector: LabelSelectorView::default(),
            template: PodTemplateSpecView::default(),
            replicas: None,
            update_strategy: None,
            pod_management_policy: None,
            revision_history_limit: None,
            volume_claim_templates: None,
            min_ready_seconds: None,
            persistent_volume_claim_retention_policy: None,
            ordinals: None,
        }
    }

    pub open spec fn with_replicas(self, replicas: int) -> VStatefulSetSpecView {
        VStatefulSetSpecView {
            replicas: Some(replicas),
            ..self
        }
    }

    pub open spec fn with_selector(self, selector: LabelSelectorView) -> VStatefulSetSpecView {
        VStatefulSetSpecView {
            selector,
            ..self
        }
    }

    pub open spec fn with_service_name(self, service_name: StringView) -> VStatefulSetSpecView {
        VStatefulSetSpecView {
            service_name,
            ..self
        }
    }

    pub open spec fn with_template(self, template: PodTemplateSpecView) -> VStatefulSetSpecView {
        VStatefulSetSpecView {
            template,
            ..self
        }
    }

    pub open spec fn with_volume_claim_templates(self, volume_claim_templates: Seq<PersistentVolumeClaimView>) -> VStatefulSetSpecView {
        VStatefulSetSpecView {
            volume_claim_templates: Some(volume_claim_templates),
            ..self
        }
    }

    pub open spec fn with_pod_management_policy(self, pod_management_policy: StringView) -> VStatefulSetSpecView {
        VStatefulSetSpecView {
            pod_management_policy: Some(pod_management_policy),
            ..self
        }
    }

    pub open spec fn with_pvc_retention_policy(self, pvc_retention_policy: StatefulSetPersistentVolumeClaimRetentionPolicyView) -> VStatefulSetSpecView {
        VStatefulSetSpecView {
            persistent_volume_claim_retention_policy: Some(pvc_retention_policy),
            ..self
        }
    }

    pub open spec fn without_pvc_retention_policy(self) -> VStatefulSetSpecView {
        VStatefulSetSpecView {
            persistent_volume_claim_retention_policy: None,
            ..self
        }
    }
}

}