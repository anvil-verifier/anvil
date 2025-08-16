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

    #[verifier(inline)]
    pub open spec fn _default() -> RoleView {
        RoleView {
            metadata: ObjectMetaView::default(),
            policy_rules: None,
        }
    }

    #[verifier(inline)]
    pub open spec fn _spec(self) -> RoleSpecView {
        self.policy_rules
    }

    #[verifier(inline)]
    pub open spec fn _status(self) -> EmptyStatusView {
        empty_status()
    }

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> RoleView {
        RoleView {
            metadata: obj.metadata,
            policy_rules: RoleView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.policy_rules is Some
            ==> (forall |i| 0 <= i < self.policy_rules->0.len() ==> #[trigger] self.policy_rules->0[i].state_validation())
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: RoleView) -> bool { true }
}

implement_resource_view_trait!(RoleView, RoleSpecView, EmptyStatusView, _default, Kind::RoleKind, _spec, _status,
    _unmarshal_helper, _state_validation, _transition_validation);

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
