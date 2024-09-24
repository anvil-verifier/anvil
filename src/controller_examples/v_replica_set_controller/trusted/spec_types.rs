// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    api_resource::*, label_selector::*, pod_template_spec::*, prelude::*,
};
use crate::kubernetes_cluster::spec::{cluster::*, cluster_state_machine::*, message::*};
use crate::v_replica_set_controller::trusted::step::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub type VRSStep = Step<VRSMessage>;

pub type VRSCluster = Cluster<VReplicaSetView, EmptyAPI, VReplicaSetReconciler>;

pub type VRSMessage = Message<EmptyTypeView, EmptyTypeView>;

pub struct VReplicaSetReconciler {}

pub struct VReplicaSetReconcileState {
    pub reconcile_step: VReplicaSetReconcileStep,
    pub filtered_pods: Option<Seq<PodView>>,
}

pub struct VReplicaSetView {
    pub metadata: ObjectMetaView,
    pub spec: VReplicaSetSpecView,
    pub status: Option<VReplicaSetStatusView>,
}

pub type VReplicaSetStatusView = EmptyStatusView;

impl VReplicaSetView {
    pub open spec fn well_formed(self) -> bool {
        &&& self.metadata.name.is_Some()
        &&& self.metadata.namespace.is_Some()
        &&& self.metadata.uid.is_Some()
        // TODO: ensure that the following is consistent with k8s's ReplicaSet
        &&& self.spec.template.is_Some()
        &&& self.spec.template.get_Some_0().metadata.is_Some()
        &&& self.spec.template.get_Some_0().spec.is_Some()
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

    open spec fn state_validation(self) -> bool {
        self.spec.replicas.is_Some() ==> self.spec.replicas.get_Some_0() >= 0
    }

    open spec fn transition_validation(self, old_obj: VReplicaSetView) -> bool {
        true
    }

}

impl CustomResourceView for VReplicaSetView {
    proof fn kind_is_custom_resource() {}

    open spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool {
        obj_spec.replicas.is_Some() ==> obj_spec.replicas.get_Some_0() >= 0
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

}
