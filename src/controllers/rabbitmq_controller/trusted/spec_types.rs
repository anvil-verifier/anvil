// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    affinity::*, api_resource::*, common::*, dynamic::*, object_meta::*, owner_reference::*,
    resource::*, resource_requirements::*, stateful_set::*, toleration::*,
};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::trusted::step::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {
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
        &&& self.metadata.name is Some
        &&& self.metadata.namespace is Some
        &&& self.metadata.uid is Some
    }

    pub open spec fn controller_owner_ref(self) -> OwnerReferenceView {
        OwnerReferenceView {
            block_owner_deletion: None,
            controller: Some(true),
            kind: Self::kind(),
            name: self.metadata.name->0,
            uid: self.metadata.uid->0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _kind() -> Kind { Kind::CustomResourceKind("rabbitmq"@) }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        &&& self.spec.replicas >= 0
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: RabbitmqClusterView) -> bool {
        &&& self.spec.replicas >= old_obj.spec.replicas
        &&& self.spec.persistence.storage == old_obj.spec.persistence.storage
        &&& self.spec.persistence.storage_class_name == old_obj.spec.persistence.storage_class_name
        &&& self.spec.pod_management_policy == old_obj.spec.pod_management_policy
    }
}

implement_resource_view_trait!(RabbitmqClusterView, RabbitmqClusterSpecView, RabbitmqClusterSpecView::default(),
    Option<RabbitmqClusterStatusView>, None, RabbitmqClusterView::_kind(), _state_validation, _transition_validation);

impl CustomResourceView for RabbitmqClusterView {
    proof fn kind_is_custom_resource() {}

    open spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool {
        RabbitmqClusterView {
            metadata: arbitrary(),
            spec: obj_spec,
            status: obj_status,
        }.state_validation()
    }

    proof fn validation_result_determined_by_spec_and_status() {}
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

impl RabbitmqClusterSpecView {
    pub open spec fn default() -> RabbitmqClusterSpecView {
        RabbitmqClusterSpecView {
            replicas: 0,
            image: ""@,
            persistence: RabbitmqClusterPersistenceSpecView::default(),
            rabbitmq_config: None,
            affinity: None,
            tolerations: None,
            labels: Map::empty(),
            annotations: Map::empty(),
            resources: None,
            pod_management_policy: ""@,
            persistent_volume_claim_retention_policy: None,
        }
    }
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

impl RabbitmqClusterPersistenceSpecView {
    pub open spec fn default() -> RabbitmqClusterPersistenceSpecView {
        RabbitmqClusterPersistenceSpecView {
            storage_class_name: ""@,
            storage: ""@,
        }
    }
}

pub uninterp spec fn random_encoded_string(length: usize) -> StringView;

}
