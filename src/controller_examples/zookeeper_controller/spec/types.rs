// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    affinity::*, api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError,
    marshal::*, object_meta::*, owner_reference::*, resource::*, resource_requirements::*,
    toleration::*,
};
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct ZookeeperClusterView {
    pub metadata: ObjectMetaView,
    pub spec: ZookeeperClusterSpecView,
}

impl ZookeeperClusterView {
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

impl ResourceView for ZookeeperClusterView {
    type Spec = ZookeeperClusterSpecView;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::CustomResourceKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> ZookeeperClusterSpecView {
        self.spec
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ZookeeperClusterView::marshal_spec(self.spec),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<ZookeeperClusterView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ZookeeperClusterView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(ZookeeperClusterView {
                metadata: obj.metadata,
                spec: ZookeeperClusterView::unmarshal_spec(obj.spec).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        ZookeeperClusterView::marshal_spec_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: ZookeeperClusterSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<ZookeeperClusterSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec() {}

    open spec fn state_validation(self) -> bool {
        &&& self.spec.replicas >= 3
    }

    open spec fn transition_validation(self, old_obj: ZookeeperClusterView) -> bool {
        &&& self.spec.ports == old_obj.spec.ports
        &&& self.spec.persistence.enabled == old_obj.spec.persistence.enabled
        &&& self.spec.persistence.storage_size == old_obj.spec.persistence.storage_size
        &&& self.spec.persistence.storage_class_name == old_obj.spec.persistence.storage_class_name
    }
}

pub struct ZookeeperClusterSpecView {
    pub replicas: int,
    pub image: StringView,
    pub ports: ZookeeperPortsView,
    pub conf: ZookeeperConfigView,
    pub persistence: ZookeeperPersistenceView,
    pub resources: Option<ResourceRequirementsView>,
    pub affinity: Option<AffinityView>,
    pub tolerations: Option<Seq<TolerationView>>,
    pub node_selector: Map<StringView, StringView>,
    pub labels: Map<StringView, StringView>,
    pub annotations: Map<StringView, StringView>,
}

impl ZookeeperClusterSpecView {}

pub struct ZookeeperPortsView {
    pub client: int,
    pub quorum: int,
    pub leader_election: int,
    pub metrics: int,
    pub admin_server: int,
}

pub struct ZookeeperConfigView {
    pub init_limit: int,
    pub tick_time: int,
    pub sync_limit: int,
    pub global_outstanding_limit: int,
    pub pre_alloc_size: int,
    pub snap_count: int,
    pub commit_log_count: int,
    pub snap_size_limit_in_kb: int,
    pub max_cnxns: int,
    pub max_client_cnxns: int,
    pub min_session_timeout: int,
    pub max_session_timeout: int,
    pub auto_purge_snap_retain_count: int,
    pub auto_purge_purge_interval: int,
    pub quorum_listen_on_all_ips: bool,
}

pub struct ZookeeperPersistenceView {
    pub enabled: bool,
    pub storage_size: StringView,
    pub storage_class_name: Option<StringView>,
}

}
