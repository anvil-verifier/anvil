// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*, object_meta::*, resource::*};
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;

verus! {

// RoleView is the ghost type of Role.


pub struct RoleView {
    pub metadata: ObjectMetaView,
    pub policy_rules: Option<Seq<PolicyRuleView>>,
}

type RoleSpecView = Option<Seq<PolicyRuleView>>;

impl RoleView {
    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> RoleView {
        RoleView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_rules(self, policy_rules: Seq<PolicyRuleView>) -> RoleView {
        RoleView {
            policy_rules: Some(policy_rules),
            ..self
        }
    }
}

impl ResourceView for RoleView {
    type Spec = RoleSpecView;
    type Status = EmptyStatusView;

    open spec fn default() -> RoleView {
        RoleView {
            metadata: ObjectMetaView::default(),
            policy_rules: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::RoleKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> RoleSpecView {
        self.policy_rules
    }

    open spec fn status(self) -> EmptyStatusView {
        empty_status()
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: RoleView::marshal_spec(self.policy_rules),
            status: RoleView::marshal_status(empty_status()),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<RoleView, UnmarshalError> {
        if obj.kind != Self::kind() {
            Err(())
        } else if !(RoleView::unmarshal_spec(obj.spec) is Ok) {
            Err(())
        } else if !(RoleView::unmarshal_status(obj.status) is Ok) {
            Err(())
        } else {
            Ok(RoleView {
                metadata: obj.metadata,
                policy_rules: RoleView::unmarshal_spec(obj.spec)->Ok_0,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        RoleView::marshal_spec_preserves_integrity();
        RoleView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    uninterp spec fn marshal_spec(s: RoleSpecView) -> Value;

    uninterp spec fn unmarshal_spec(v: Value) -> Result<RoleSpecView, UnmarshalError>;

    uninterp spec fn marshal_status(s: EmptyStatusView) -> Value;

    uninterp spec fn unmarshal_status(v: Value) -> Result<EmptyStatusView, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        &&& self.policy_rules is Some
            ==> (forall |i| 0 <= i < self.policy_rules->0.len() ==> #[trigger] self.policy_rules->0[i].state_validation())
    }

    open spec fn transition_validation(self, old_obj: RoleView) -> bool {
        true
    }
}

pub struct PolicyRuleView {
    pub api_groups: Option<Seq<StringView>>,
    pub resources: Option<Seq<StringView>>,
    pub verbs: Seq<StringView>,
}

impl PolicyRuleView {
    pub open spec fn default() -> PolicyRuleView {
        PolicyRuleView {
            api_groups: None,
            resources: None,
            verbs: Seq::empty(),
        }
    }

    pub open spec fn state_validation(self) -> bool {
        &&& self.api_groups is Some
        &&& self.api_groups->0.len() > 0
        &&& self.resources is Some
        &&& self.resources->0.len() > 0
        &&& self.verbs.len() > 0
    }

    pub open spec fn with_api_groups(self, api_groups: Seq<StringView>) -> PolicyRuleView {
        PolicyRuleView {
            api_groups: Some(api_groups),
            ..self
        }
    }

    pub open spec fn with_resources(self, resources: Seq<StringView>) -> PolicyRuleView {
        PolicyRuleView {
            resources: Some(resources),
            ..self
        }
    }

    pub open spec fn with_verbs(self, verbs: Seq<StringView>) -> PolicyRuleView {
        PolicyRuleView {
            verbs: verbs,
            ..self
        }
    }
}

}
