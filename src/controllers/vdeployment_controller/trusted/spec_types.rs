// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    label_selector::*, pod_template_spec::*, prelude::*,
};
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;

verus! {

pub struct VDeploymentView {
    pub metadata: ObjectMetaView,
    pub spec: VDeploymentSpecView,
    pub status: Option<VDeploymentStatusView>,
}

pub type VDeploymentStatusView = EmptyStatusView;

impl VDeploymentView {

    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> VDeploymentView {
        VDeploymentView {
            metadata: metadata,
            ..self
        }
    }

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
}

impl ResourceView for VDeploymentView {
    type Spec = VDeploymentSpecView;
    type Status = Option<VDeploymentStatusView>;

    open spec fn default() -> VDeploymentView {
        VDeploymentView {
            metadata: ObjectMetaView::default(),
            spec: arbitrary(), // TODO: specify the default value for spec
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView { self.metadata }

    open spec fn kind() -> Kind { Kind::CustomResourceKind("vdeployment"@) }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> VDeploymentSpecView { self.spec }

    open spec fn status(self) -> Option<VDeploymentStatusView> { self.status }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: VDeploymentView::marshal_spec(self.spec),
            status: VDeploymentView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<VDeploymentView, UnmarshalError> {
        if obj.kind != Self::kind() {
            Err(())
        } else if !(VDeploymentView::unmarshal_spec(obj.spec) is Ok) {
            Err(())
        } else if !(VDeploymentView::unmarshal_status(obj.status) is Ok) {
            Err(())
        } else {
            Ok(VDeploymentView {
                metadata: obj.metadata,
                spec: VDeploymentView::unmarshal_spec(obj.spec)->Ok_0,
                status: VDeploymentView::unmarshal_status(obj.status)->Ok_0,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        VDeploymentView::marshal_spec_preserves_integrity();
        VDeploymentView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    uninterp spec fn marshal_spec(s: VDeploymentSpecView) -> Value;

    uninterp spec fn unmarshal_spec(v: Value) -> Result<VDeploymentSpecView, UnmarshalError>;

    uninterp spec fn marshal_status(s: Option<VDeploymentStatusView>) -> Value;

    uninterp spec fn unmarshal_status(v: Value) -> Result<Option<VDeploymentStatusView>, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    // TODO: keep it consistent with k8s's Deployment
    open spec fn state_validation(self) -> bool {
        // replicas is non-negative
        &&& self.spec.replicas is Some ==> self.spec.replicas->0 >= 0

        // minReadySeconds is non-negative
        &&& match (self.spec.min_ready_seconds, self.spec.progress_deadline_seconds) {
            // minReadySeconds and should be less than progressDeadlineSeconds
            (Some(min), Some(deadline)) => min < deadline && min >= 0,
            // minReadySeconds should be less than the default value of progressDeadlineSeconds 600
            (Some(min), None) => min < 600 && min >= 0,
            // progressDeadlineSeconds should be greater than the default value of minReadySeconds 0
            (None, Some(deadline)) => deadline > 0,
            (None, None) => true,
        }

        // If strategy provided, it should be Recreate or RollingUpdate
        &&& self.spec.strategy is Some ==> {
            (
                self.spec.strategy->0.type_ is Some ==> (
                    (
                        self.spec.strategy->0.type_->0 == "Recreate"@
                        // rollingUpdate block only appear when type == "RollingUpdate"
                        && self.spec.strategy->0.rolling_update is None
                    )
                    || (
                        // maxSurge and maxUnavailable cannot both exist and be 0
                        self.spec.strategy->0.type_->0 == "RollingUpdate"@
                        && (self.spec.strategy->0.rolling_update is Some ==>
                            match (self.spec.strategy->0.rolling_update->0.max_surge, self.spec.strategy->0.rolling_update->0.max_unavailable) {
                                (Some(max_surge), Some(max_unavailable)) => max_surge >= 0 && max_unavailable >= 0 && !(max_surge == 0 && max_unavailable == 0),
                                (Some(max_surge), None) => max_surge >= 0,
                                (None, Some(max_unavailable)) => max_unavailable >= 0,
                                (None, None) => true,
                            }
                        )
                    )
                )
            )
        }

        // selector exists, and its match_labels is not empty
        // TODO: revise it after supporting selector.match_expressions
        &&& self.spec.selector.match_labels is Some
        &&& self.spec.selector.match_labels->0.len() > 0
        // template and its metadata ane spec exists
        &&& self.spec.template.metadata is Some
        // can be derived from selector match labels
        &&& self.spec.template.metadata->0.labels is Some
        &&& self.spec.template.spec is Some
        // selector matches template's metadata's labels
        &&& self.spec.selector.matches(self.spec.template.metadata->0.labels->0)
    }


    open spec fn transition_validation(self, old_obj: VDeploymentView) -> bool {
        true
    }
}

impl CustomResourceView for VDeploymentView {
    proof fn kind_is_custom_resource() {}

    open spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool {
        VDeploymentView {
            metadata: arbitrary(),
            spec: obj_spec,
            status: obj_status,
        }.state_validation()
    }

    proof fn validation_result_determined_by_spec_and_status() {}
}

// DEPLOYMENT STRATEGY SPEC IMPLEMENTATION
pub struct DeploymentStrategyView {
    pub type_: Option<StringView>,
    pub rolling_update: Option<RollingUpdateDeploymentView>,
}

impl DeploymentStrategyView {
    pub open spec fn default() -> DeploymentStrategyView {
        DeploymentStrategyView {
            type_: None,
            rolling_update: None,
        }
    }
    pub open spec fn with_type(self, type_: StringView) -> DeploymentStrategyView {
        DeploymentStrategyView {
            type_: Some(type_),
            ..self
        }
    }

    pub open spec fn with_rolling_update(self, rolling_update: RollingUpdateDeploymentView) -> DeploymentStrategyView {
        DeploymentStrategyView {
            rolling_update: Some(rolling_update),
            ..self
        }
    }
}

pub struct RollingUpdateDeploymentView {
    pub max_surge: Option<int>,
    pub max_unavailable: Option<int>,
}

impl RollingUpdateDeploymentView {
    pub open spec fn default() -> RollingUpdateDeploymentView {
        RollingUpdateDeploymentView {
            max_surge: None,
            max_unavailable: None,
        }
    }
    pub open spec fn with_max_surge(self, max_surge: int) -> RollingUpdateDeploymentView {
        RollingUpdateDeploymentView {
            max_surge: Some(max_surge),
            ..self
        }
    }

    pub open spec fn with_max_unavailable(self, max_unavailable: int) -> RollingUpdateDeploymentView {
        RollingUpdateDeploymentView {
            max_unavailable: Some(max_unavailable),
            ..self
        }
    }
}
// END DEPLOYMENT STRATEGY SPEC IMPLEMENTATION

pub struct VDeploymentSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub template: PodTemplateSpecView,
    pub min_ready_seconds: Option<int>,
    pub progress_deadline_seconds: Option<int>,
    pub strategy: Option<DeploymentStrategyView>,
    pub revision_history_limit: Option<int>,
    pub paused: Option<bool>
}

}
