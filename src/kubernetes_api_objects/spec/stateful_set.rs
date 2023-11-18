// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, label_selector::*, marshal::*, object_meta::*,
    persistent_volume_claim::*, pod_template_spec::*, resource::*,
};
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

/// StatefulSetView is the ghost type of StatefulSet.
/// It is supposed to be used in spec and proof code.

pub struct StatefulSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<StatefulSetSpecView>,
    pub status: Option<StatefulSetStatusView>,
}

impl StatefulSetView {
    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> StatefulSetView {
        StatefulSetView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: StatefulSetSpecView) -> StatefulSetView {
        StatefulSetView {
            spec: Some(spec),
            ..self
        }
    }
}

impl ResourceView for StatefulSetView {
    type Spec = Option<StatefulSetSpecView>;
    type Status = Option<StatefulSetStatusView>;

    open spec fn default() -> StatefulSetView {
        StatefulSetView {
            metadata: ObjectMetaView::default(),
            spec: None,
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::StatefulSetKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<StatefulSetSpecView> {
        self.spec
    }

    open spec fn status(self) -> Option<StatefulSetStatusView> {
        self.status
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: StatefulSetView::marshal_spec(self.spec),
            status: StatefulSetView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<StatefulSetView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !StatefulSetView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !StatefulSetView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(StatefulSetView {
                metadata: obj.metadata,
                spec: StatefulSetView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: StatefulSetView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        StatefulSetView::marshal_spec_preserves_integrity();
        StatefulSetView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: Option<StatefulSetSpecView>) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<Option<StatefulSetSpecView>, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<StatefulSetStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<StatefulSetStatusView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        let new_spec = self.spec.get_Some_0();
        &&& self.spec.is_Some()
        &&& new_spec.replicas.is_Some() ==> new_spec.replicas.get_Some_0() >= 0
        // &&& new_spec.pod_management_policy.is_Some()
        //     ==> (new_spec.pod_management_policy.get_Some_0() == new_strlit("OrderedReady")@
        //         || new_spec.pod_management_policy.get_Some_0() == new_strlit("Parallel")@)
        // &&& new_spec.persistent_volume_claim_retention_policy.is_Some()
        //     ==> new_spec.persistent_volume_claim_retention_policy.get_Some_0().state_validation()
    }

    open spec fn transition_validation(self, old_obj: StatefulSetView) -> bool {
        let old_spec = old_obj.spec.get_Some_0();
        let new_spec = self.spec.get_Some_0();
        // Fields other than replicas, template, persistent_volume_claim_retention_policy
        // (and some other unspecified fields) are immutable.
        &&& old_spec == StatefulSetSpecView {
            replicas: old_spec.replicas,
            template: old_spec.template,
            persistent_volume_claim_retention_policy: old_spec.persistent_volume_claim_retention_policy,
            ..new_spec
        }
    }
}

pub struct StatefulSetSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub service_name: StringView,
    pub template: PodTemplateSpecView,
    pub volume_claim_templates: Option<Seq<PersistentVolumeClaimView>>,
    pub pod_management_policy: Option<StringView>,
    pub persistent_volume_claim_retention_policy: Option<StatefulSetPersistentVolumeClaimRetentionPolicyView>,
}

impl StatefulSetSpecView {
    pub open spec fn default() -> StatefulSetSpecView {
        StatefulSetSpecView {
            replicas: None,
            selector: LabelSelectorView::default(),
            service_name: new_strlit("")@,
            template: PodTemplateSpecView::default(),
            volume_claim_templates: None,
            pod_management_policy: None,
            persistent_volume_claim_retention_policy: None,
        }
    }

    pub open spec fn set_replicas(self, replicas: int) -> StatefulSetSpecView {
        StatefulSetSpecView {
            replicas: Some(replicas),
            ..self
        }
    }

    pub open spec fn set_selector(self, selector: LabelSelectorView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            selector: selector,
            ..self
        }
    }

    pub open spec fn set_service_name(self, service_name: StringView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            service_name: service_name,
            ..self
        }
    }

    pub open spec fn set_template(self, template: PodTemplateSpecView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            template: template,
            ..self
        }
    }

    pub open spec fn set_volume_claim_templates(self, volume_claim_templates: Seq<PersistentVolumeClaimView>) -> StatefulSetSpecView {
        StatefulSetSpecView {
            volume_claim_templates: Some(volume_claim_templates),
            ..self
        }
    }

    pub open spec fn set_pod_management_policy(self, pod_management_policy: StringView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            pod_management_policy: Some(pod_management_policy),
            ..self
        }
    }

    pub open spec fn set_pvc_retention_policy(self, pvc_retention_policy: StatefulSetPersistentVolumeClaimRetentionPolicyView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            persistent_volume_claim_retention_policy: Some(pvc_retention_policy),
            ..self
        }
    }

    pub open spec fn unset_pvc_retention_policy(self) -> StatefulSetSpecView {
        StatefulSetSpecView {
            persistent_volume_claim_retention_policy: None,
            ..self
        }
    }
}

pub struct StatefulSetPersistentVolumeClaimRetentionPolicyView {
    pub when_deleted: Option<StringView>,
    pub when_scaled: Option<StringView>,
}

impl StatefulSetPersistentVolumeClaimRetentionPolicyView {
    pub open spec fn default() -> StatefulSetPersistentVolumeClaimRetentionPolicyView {
        StatefulSetPersistentVolumeClaimRetentionPolicyView {
            when_deleted: None,
            when_scaled: None,
        }
    }

    pub open spec fn state_validation(self) -> bool {
        &&& self.when_deleted.is_Some() ==> (self.when_deleted.get_Some_0() == new_strlit("Retain")@ || self.when_deleted.get_Some_0() == new_strlit("Delete")@)
        &&& self.when_scaled.is_Some() ==> (self.when_scaled.get_Some_0() == new_strlit("Retain")@ || self.when_scaled.get_Some_0() == new_strlit("Delete")@)
    }

    pub open spec fn set_when_deleted(self, when_deleted: StringView) -> StatefulSetPersistentVolumeClaimRetentionPolicyView {
        StatefulSetPersistentVolumeClaimRetentionPolicyView {
            when_deleted: Some(when_deleted),
            ..self
        }
    }

    pub open spec fn set_when_scaled(self, when_scaled: StringView) -> StatefulSetPersistentVolumeClaimRetentionPolicyView {
        StatefulSetPersistentVolumeClaimRetentionPolicyView {
            when_scaled: Some(when_scaled),
            ..self
        }
    }
}

pub struct StatefulSetStatusView {
    pub ready_replicas: Option<int>,
}

}
