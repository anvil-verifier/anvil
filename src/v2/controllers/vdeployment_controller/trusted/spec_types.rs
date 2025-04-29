// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    api_resource::*, label_selector::*, pod_template_spec::*, prelude::*,
};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::vdeployment_controller::trusted::step::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct VDeploymentView {
    pub metadata: ObjectMetaView,
    pub spec: VDeploymentSpecView,
    pub status: Option<VDeploymentStatusView>,
}

pub type VDeploymentStatusView = EmptyStatusView;

impl VDeploymentView {
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
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
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
        } else if !VDeploymentView::unmarshal_spec(obj.spec).is_Ok() {
            Err(())
        } else if !VDeploymentView::unmarshal_status(obj.status).is_Ok() {
            Err(())
        } else {
            Ok(VDeploymentView {
                metadata: obj.metadata,
                spec: VDeploymentView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: VDeploymentView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        VDeploymentView::marshal_spec_preserves_integrity();
        VDeploymentView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: VDeploymentSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<VDeploymentSpecView, UnmarshalError>;

    closed spec fn marshal_status(s: Option<VDeploymentStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<VDeploymentStatusView>, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    // TODO: keep it consistent with k8s's Deployment
    open spec fn state_validation(self) -> bool {
        // replicas is non-negative
        &&& self.spec.replicas.is_Some() ==> self.spec.replicas.get_Some_0() >= 0
        
        // minReadySeconds, if present, must be non‑negative
        &&& self.spec.minReadySeconds.is_Some() ==>
            self.spec.minReadySeconds.get_Some_0() >= 0
        
        // progressDeadlineSeconds, if present, must be ≥ 0
        &&& self.spec.progressDeadlineSeconds.is_Some() ==>
            self.spec.progressDeadlineSeconds.get_Some_0() >= 0
        
        // If strategy provided, it should be Recreate or RollingUpdate
        &&& self.spec.strategy.is_Some() ==> {
            (
                self.spec.strategy.get_Some_0().type_.is_Some() ==> (
                    (
                        self.spec.strategy.get_Some_0().type_.get_Some_0() == "Recreate"@
                        // RollingUpdate block only appear when type == "RollingUpdate"
                        && self.spec.strategy.get_Some_0().rollingUpdate.is_None()
                    )
                    ||
                    (
                        self.spec.strategy.get_Some_0().type_.get_Some_0() == "RollingUpdate"@
                        // ==> self.spec.strategy.get_Some_0().rollingUpdate.is_Some()
                        // && (
                        //     self.spec.strategy.get_Some_0().rollingUpdate.get_Some_0().maxSurge.is_Some()
                        //     // ==> (
                        //     //     self.spec.strategy.get_Some_0().rollingUpdate.get_Some_0().maxSurge.get_Some_0() != 0
                        //     // )
                        //     // ||
                        //     // self.spec.strategy.get_Some_0().rollingUpdate.get_Some_0().maxUnavailable.is_Some() ==> (
                        //     //     self.spec.strategy.get_Some_0().rollingUpdate.get_Some_0().maxUnavailable.get_Some_0() != 0
                        //     // )
                        // )
                    )
                )
            )
        }

        // selector exists, and its match_labels is not empty
        // TODO: revise it after supporting selector.match_expressions
        &&& self.spec.selector.match_labels.is_Some()
        &&& self.spec.selector.match_labels.get_Some_0().len() > 0
        // template and its metadata ane spec exists
        &&& self.spec.template.is_Some()
        &&& self.spec.template.get_Some_0().metadata.is_Some()
        &&& self.spec.template.get_Some_0().spec.is_Some()
        // selector matches template's metadata's labels
        &&& self.spec.selector.matches(self.spec.template.get_Some_0().metadata.get_Some_0().labels.unwrap_or(Map::empty()))
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
    pub rollingUpdate: Option<RollingUpdateDeploymentView>,
}

impl DeploymentStrategyView {
    pub open spec fn default() -> DeploymentStrategyView {
        DeploymentStrategyView {
            type_: None,
            rollingUpdate: None,
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
            rollingUpdate: Some(rolling_update),
            ..self
        }
    }
}

pub struct RollingUpdateDeploymentView {
    pub maxSurge: Option<int>,
    pub maxUnavailable: Option<int>,
}

impl RollingUpdateDeploymentView {
    pub open spec fn default() -> RollingUpdateDeploymentView {
        RollingUpdateDeploymentView {
            maxSurge: None,
            maxUnavailable: None,
        }
    }
    pub open spec fn with_max_surge(self, max_surge: int) -> RollingUpdateDeploymentView {
        RollingUpdateDeploymentView {
            maxSurge: Some(max_surge),
            ..self
        }
    }

    pub open spec fn with_max_unavailable(self, max_unavailable: int) -> RollingUpdateDeploymentView {
        RollingUpdateDeploymentView {
            maxUnavailable: Some(max_unavailable),
            ..self
        }
    }
}
// END DEPLOYMENT STRATEGY SPEC IMPLEMENTATION

pub struct VDeploymentSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub template: Option<PodTemplateSpecView>,
    pub minReadySeconds: Option<int>,
    pub progressDeadlineSeconds: Option<int>,
    pub strategy: Option<DeploymentStrategyView>,
    pub revisionHistoryLimit: Option<int>,
    pub paused: Option<bool>
}

}
