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

impl ResourceView for VReplicaSetView {
    type Spec = VReplicaSetSpecView;
    type Status = Option<VReplicaSetStatusView>;

    open spec fn default() -> VReplicaSetView {
        VReplicaSetView {
            metadata: ObjectMetaView::default(),
            spec: arbitrary(), // TODO: specify the default value for spec
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView { self.metadata }

    open spec fn kind() -> Kind { Kind::CustomResourceKind("vreplicaset"@) }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> VReplicaSetSpecView { self.spec }

    open spec fn status(self) -> Option<VReplicaSetStatusView> { self.status }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: VReplicaSetView::marshal_spec(self.spec),
            status: VReplicaSetView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<VReplicaSetView, UnmarshalError> {
        if obj.kind != Self::kind() {
            Err(())
        } else if !VReplicaSetView::unmarshal_spec(obj.spec).is_Ok() {
            Err(())
        } else if !VReplicaSetView::unmarshal_status(obj.status).is_Ok() {
            Err(())
        } else {
            Ok(VReplicaSetView {
                metadata: obj.metadata,
                spec: VReplicaSetView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: VReplicaSetView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        VReplicaSetView::marshal_spec_preserves_integrity();
        VReplicaSetView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: VReplicaSetSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<VReplicaSetSpecView, UnmarshalError>;

    closed spec fn marshal_status(s: Option<VReplicaSetStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<VReplicaSetStatusView>, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    // TODO: keep it consistent with k8s's ReplicaSet
    open spec fn state_validation(self) -> bool {
        // replicas is non-negative
        &&& self.spec.replicas.is_Some() ==> self.spec.replicas.get_Some_0() >= 0
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

    open spec fn transition_validation(self, old_obj: VReplicaSetView) -> bool {
        true
    }
}

impl CustomResourceView for VReplicaSetView {
    proof fn kind_is_custom_resource() {}

    open spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool {
        VReplicaSetView {
            metadata: arbitrary(),
            spec: obj_spec,
            status: obj_status,
        }.state_validation()
    }

    proof fn validation_result_determined_by_spec_and_status() {}
}

pub struct VReplicaSetSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub template: Option<PodTemplateSpecView>,
}

}
