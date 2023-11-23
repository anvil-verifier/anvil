// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    affinity::*, common::*, container::*, dynamic::*, marshal::*, object_meta::*, resource::*,
    resource_requirements::*, toleration::*, volume::*,
};
use crate::vstd_ext::{string_map::*, string_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

/// PodView is the ghost type of Pod.
/// It is supposed to be used in spec and proof code.

pub struct PodView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PodSpecView>,
    pub status: Option<PodStatusView>,
}

pub type PodStatusView = EmptyStatusView;

impl PodView {
    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> PodView {
        PodView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: PodSpecView) -> PodView {
        PodView {
            spec: Some(spec),
            ..self
        }
    }
}

impl ResourceView for PodView {
    type Spec = Option<PodSpecView>;
    type Status = Option<PodStatusView>;

    open spec fn default() -> PodView {
        PodView {
            metadata: ObjectMetaView::default(),
            spec: None,
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::PodKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<PodSpecView> {
        self.spec
    }

    open spec fn status(self) -> Option<PodStatusView> {
        self.status
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: PodView::marshal_spec(self.spec),
            status: PodView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<PodView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !PodView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !PodView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(PodView {
                metadata: obj.metadata,
                spec: PodView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: PodView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        PodView::marshal_spec_preserves_integrity();
        PodView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: Option<PodSpecView>) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<Option<PodSpecView>, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<PodStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<PodStatusView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity(){}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        &&& self.spec.is_Some()
    }

    open spec fn transition_validation(self, old_obj: PodView) -> bool {
        true
    }
}

pub struct PodSpecView {
    pub affinity: Option<AffinityView>,
    pub containers: Seq<ContainerView>,
    pub volumes: Option<Seq<VolumeView>>,
    pub init_containers: Option<Seq<ContainerView>>,
    pub service_account_name: Option<StringView>,
    pub tolerations: Option<Seq<TolerationView>>,
    pub node_selector: Option<Map<StringView, StringView>>,
    pub runtime_class_name: Option<StringView>,
    pub dns_policy: Option<StringView>,
    pub priority_class_name: Option<StringView>,
    pub scheduler_name: Option<StringView>,
    pub security_context: Option<PodSecurityContextView>,
    pub host_network: Option<bool>,
    pub termination_grace_period_seconds: Option<int>,
    pub image_pull_secrets: Option<Seq<LocalObjectReferenceView>>,
}

impl PodSpecView {
    pub open spec fn default() -> PodSpecView {
        PodSpecView {
            affinity: None,
            containers: Seq::empty(),
            volumes: None,
            init_containers: None,
            service_account_name: None,
            tolerations: None,
            node_selector: None,
            runtime_class_name: None,
            dns_policy: None,
            priority_class_name: None,
            scheduler_name: None,
            security_context: None,
            host_network: None,
            termination_grace_period_seconds: None,
            image_pull_secrets: None,
        }
    }

    pub open spec fn set_affinity(self, affinity: AffinityView) -> PodSpecView {
        PodSpecView {
            affinity: Some(affinity),
            ..self
        }
    }

    pub open spec fn unset_affinity(self) -> PodSpecView {
        PodSpecView {
            affinity: None,
            ..self
        }
    }

    pub open spec fn set_containers(self, containers: Seq<ContainerView>) -> PodSpecView {
        PodSpecView {
            containers: containers,
            ..self
        }
    }

    pub open spec fn set_volumes(self, volumes: Seq<VolumeView>) -> PodSpecView {
        PodSpecView {
            volumes: Some(volumes),
            ..self
        }
    }

    pub open spec fn set_init_containers(self, init_containers: Seq<ContainerView>) -> PodSpecView {
        PodSpecView {
            init_containers: Some(init_containers),
            ..self
        }
    }

    pub open spec fn set_service_account_name(self, service_account_name: StringView) -> PodSpecView {
        PodSpecView {
            service_account_name: Some(service_account_name),
            ..self
        }
    }

    pub open spec fn set_tolerations(self, tolerations: Seq<TolerationView>) -> PodSpecView {
        PodSpecView {
            tolerations: Some(tolerations),
            ..self
        }
    }

    pub open spec fn unset_tolerations(self) -> PodSpecView {
        PodSpecView {
            tolerations: None,
            ..self
        }
    }

    pub open spec fn set_node_selector(self, node_selector: Map<StringView, StringView>) -> PodSpecView {
        PodSpecView {
            node_selector: Some(node_selector),
            ..self
        }
    }

    pub open spec fn overwrite_runtime_class_name(self, runtime_class_name: Option<StringView>) -> PodSpecView {
        PodSpecView {
            runtime_class_name: runtime_class_name,
            ..self
        }
    }

    pub open spec fn overwrite_dns_policy(self, dns_policy: Option<StringView>) -> PodSpecView {
        PodSpecView {
            dns_policy: dns_policy,
            ..self
        }
    }

    pub open spec fn overwrite_scheduler_name(self, scheduler_name: Option<StringView>) -> PodSpecView {
        PodSpecView {
            scheduler_name: scheduler_name,
            ..self
        }
    }

    pub open spec fn overwrite_priority_class_name(self, priority_class_name: Option<StringView>) -> PodSpecView {
        PodSpecView {
            priority_class_name: priority_class_name,
            ..self
        }
    }

    pub open spec fn set_security_context(self, security_context: PodSecurityContextView) -> PodSpecView {
        PodSpecView {
            security_context: Some(security_context),
            ..self
        }
    }

    pub open spec fn set_host_network(self, host_network: bool) -> PodSpecView {
        PodSpecView {
            host_network: Some(host_network),
            ..self
        }
    }

    pub open spec fn set_termination_grace_period_seconds(self, termination_grace_period_seconds: int) -> PodSpecView {
        PodSpecView {
            termination_grace_period_seconds: Some(termination_grace_period_seconds),
            ..self
        }
    }

    pub open spec fn set_image_pull_secrets(self, image_pull_secrets: Seq<LocalObjectReferenceView>) -> PodSpecView {
        PodSpecView {
            image_pull_secrets: Some(image_pull_secrets),
            ..self
        }
    }
}

pub struct PodSecurityContextView {}

pub struct LocalObjectReferenceView {}

}
