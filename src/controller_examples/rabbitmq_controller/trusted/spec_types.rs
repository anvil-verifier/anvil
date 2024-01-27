// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    affinity::*, api_resource::*, common::*, dynamic::*, marshal::*, object_meta::*,
    owner_reference::*, resource::*, resource_requirements::*, stateful_set::*, toleration::*,
};
use crate::kubernetes_cluster::spec::{cluster::*, cluster_state_machine::*, message::*};
use crate::rabbitmq_controller::trusted::step::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub type RMQStep = Step<RMQMessage>;

pub type RMQCluster = Cluster<RabbitmqClusterView, EmptyAPI, RabbitmqReconciler>;

pub type RMQMessage = Message<EmptyTypeView, EmptyTypeView>;

pub struct RabbitmqReconciler {}

pub struct RabbitmqReconcileState {
    pub reconcile_step: RabbitmqReconcileStep,
    pub latest_config_map_rv_opt: Option<StringView>,
}

pub struct RabbitmqClusterView {
    pub metadata: ObjectMetaView,
    pub spec: RabbitmqClusterSpecView,
    pub status: Option<RabbitmqClusterStatusView>,
}

pub type RabbitmqClusterStatusView = EmptyStatusView;

impl RabbitmqClusterView {
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

impl ResourceView for RabbitmqClusterView {
    type Spec = RabbitmqClusterSpecView;
    type Status = Option<RabbitmqClusterStatusView>;

    open spec fn default() -> RabbitmqClusterView {
        RabbitmqClusterView {
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

    open spec fn spec(self) -> RabbitmqClusterSpecView { self.spec }

    open spec fn status(self) -> Option<RabbitmqClusterStatusView> { self.status }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: RabbitmqClusterView::marshal_spec(self.spec),
            status: RabbitmqClusterView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<RabbitmqClusterView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !RabbitmqClusterView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !RabbitmqClusterView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(RabbitmqClusterView {
                metadata: obj.metadata,
                spec: RabbitmqClusterView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: RabbitmqClusterView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        RabbitmqClusterView::marshal_spec_preserves_integrity();
        RabbitmqClusterView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: RabbitmqClusterSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<RabbitmqClusterSpecView, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<RabbitmqClusterStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<RabbitmqClusterStatusView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        &&& self.spec.replicas >= 0
        // &&& self.spec.pod_management_policy.is_Some() ==>
        //     (self.spec.pod_management_policy.get_Some_0() == new_strlit("OrderedReady")@
        //         || self.spec.pod_management_policy.get_Some_0() == new_strlit("Parallel")@)
        // &&& self.spec.persistent_volume_claim_retention_policy.is_Some() ==>
        //     self.spec.persistent_volume_claim_retention_policy.get_Some_0().state_validation()
    }

    open spec fn transition_validation(self, old_obj: RabbitmqClusterView) -> bool {
        &&& self.spec.replicas >= old_obj.spec.replicas
        &&& self.spec.persistence.storage == old_obj.spec.persistence.storage
        &&& self.spec.persistence.storage_class_name == old_obj.spec.persistence.storage_class_name
        &&& self.spec.pod_management_policy == old_obj.spec.pod_management_policy
    }

}

impl CustomResourceView for RabbitmqClusterView {
    proof fn kind_is_custom_resource() {}
}

pub struct RabbitmqClusterSpecView {
    pub replicas: int,
    pub image: StringView,
    pub persistence: RabbitmqClusterPersistenceSpecView,
    pub rabbitmq_config: Option<RabbitmqConfigView>,
    pub affinity: Option<AffinityView>,
    pub tolerations: Option<Seq<TolerationView>>,
    pub labels: Map<StringView, StringView>,
    pub annotations: Map<StringView, StringView>,
    pub resources: Option<ResourceRequirementsView>,
    pub pod_management_policy: StringView,
    pub persistent_volume_claim_retention_policy: Option<StatefulSetPersistentVolumeClaimRetentionPolicyView>,
}

pub struct RabbitmqConfigView {
    pub additional_config: Option<StringView>,
    pub advanced_config: Option<StringView>,
    pub env_config: Option<StringView>,
}

pub struct RabbitmqClusterPersistenceSpecView {
    pub storage_class_name: StringView,
    pub storage: StringView,
}

pub closed spec fn random_encoded_string(length: usize) -> StringView;

}
