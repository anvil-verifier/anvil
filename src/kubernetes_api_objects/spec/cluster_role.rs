// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, marshal::*, object_meta::*, resource::*, role::*,
};
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

/// ClusterRoleView is the ghost type of ClusterRole.
/// It is supposed to be used in spec and proof code.

pub struct ClusterRoleView {
    pub metadata: ObjectMetaView,
    pub policy_rules: Option<Seq<PolicyRuleView>>,
}

type ClusterRoleSpecView = (Option<Seq<PolicyRuleView>>, ());

impl ClusterRoleView {
    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> ClusterRoleView {
        ClusterRoleView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_policy_rules(self, policy_rules: Seq<PolicyRuleView>) -> ClusterRoleView {
        ClusterRoleView {
            policy_rules: Some(policy_rules),
            ..self
        }
    }
}

impl ResourceView for ClusterRoleView {
    type Spec = ClusterRoleSpecView;
    type Status = EmptyStatusView;

    open spec fn default() -> ClusterRoleView {
        ClusterRoleView {
            metadata: ObjectMetaView::default(),
            policy_rules: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::ClusterRoleKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> ClusterRoleSpecView {
        (self.policy_rules, ())
    }

    open spec fn status(self) -> EmptyStatusView {
        empty_status()
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ClusterRoleView::marshal_spec((self.policy_rules, ())),
            status: ClusterRoleView::marshal_status(empty_status()),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<ClusterRoleView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ClusterRoleView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ClusterRoleView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(ClusterRoleView {
                metadata: obj.metadata,
                policy_rules: ClusterRoleView::unmarshal_spec(obj.spec).get_Ok_0().0,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        ClusterRoleView::marshal_spec_preserves_integrity();
        ClusterRoleView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: ClusterRoleSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<ClusterRoleSpecView, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: EmptyStatusView) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<EmptyStatusView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        true
    }

    open spec fn transition_validation(self, old_obj: ClusterRoleView) -> bool {
        true
    }
}

}
