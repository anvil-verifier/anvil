// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{label_selector::*, pod_template_spec::*, prelude::*};
use vstd::prelude::*;

verus! {

pub struct VReplicaSetView {
    pub metadata: ObjectMetaView,
    pub spec: VReplicaSetSpecView,
    pub status: Option<VReplicaSetStatusView>,
}

pub type VReplicaSetStatusView = EmptyStatusView;

impl VReplicaSetView {
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

    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> VReplicaSetView {
        VReplicaSetView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_spec(self, spec: VReplicaSetSpecView) -> VReplicaSetView {
        VReplicaSetView {
            spec: spec,
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn _kind() -> Kind { Kind::CustomResourceKind("vreplicaset"@) }

    // TODO: keep it consistent with k8s's ReplicaSet
    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        // replicas is non-negative
        &&& self.spec.replicas is Some ==> self.spec.replicas->0 >= 0
        // selector exists, and its match_labels is not empty
        // TODO: revise it after supporting selector.match_expressions
        &&& self.spec.selector.match_labels is Some
        // labels are finite
        &&& self.spec.selector.match_labels->0.dom().finite()
        &&& self.spec.selector.match_labels->0.len() > 0
        // template, and its metadata ane spec exists
        &&& self.spec.template is Some
        &&& self.spec.template->0.metadata is Some
        &&& self.spec.template->0.spec is Some
        // kubernetes requires selector matches template's metadata's labels
        // and also requires selector to be non-empty, so it implicitly requires that the labels are non-empty
        &&& self.spec.template->0.metadata->0.labels is Some
        &&& self.spec.template->0.metadata->0.labels->0.dom().finite()
        &&& self.spec.selector.matches(self.spec.template->0.metadata->0.labels->0)
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: VReplicaSetView) -> bool {
        true
    }
}

implement_resource_view_trait!(VReplicaSetView, VReplicaSetSpecView, VReplicaSetSpecView::default(),
    Option<VReplicaSetStatusView>, None, VReplicaSetView::_kind(), _state_validation, _transition_validation);

impl CustomResourceView for VReplicaSetView {
    proof fn kind_is_custom_resource() {}

    open spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool {
        VReplicaSetView {
            metadata: arbitrary(),
            spec: obj_spec,
            status: obj_status,
        }.state_validation()
    }

    proof fn validation_result_determined_by_spec_and_status()
        ensures forall |obj: Self| #[trigger] obj.state_validation() == Self::spec_status_validation(obj.spec(), obj.status())
    {}
}

pub struct VReplicaSetSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub template: Option<PodTemplateSpecView>,
}

impl VReplicaSetSpecView {
    pub open spec fn default() -> VReplicaSetSpecView {
        VReplicaSetSpecView {
            replicas: None,
            selector: LabelSelectorView::default(),
            template: None,
        }
    }

    pub open spec fn with_replicas(self, replicas: int) -> VReplicaSetSpecView {
        VReplicaSetSpecView {
            replicas: Some(replicas),
            ..self
        }
    }

    pub open spec fn with_selector(self, selector: LabelSelectorView) -> VReplicaSetSpecView {
        VReplicaSetSpecView {
            selector: selector,
            ..self
        }
    }

    pub open spec fn with_template(self, template: PodTemplateSpecView) -> VReplicaSetSpecView {
        VReplicaSetSpecView {
            template: Some(template),
            ..self
        }
    }
}

}
