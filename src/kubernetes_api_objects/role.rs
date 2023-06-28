// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

/// This definition is a wrapper of Role defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/rbac/v1/role.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/reference/access-authn-authz/rbac/.

#[verifier(external_body)]
pub struct Role {
    inner: deps_hack::k8s_openapi::api::rbac::v1::Role,
}

impl Role {
    pub spec fn view(&self) -> RoleView;

    #[verifier(external_body)]
    pub fn default() -> (role: Role)
        ensures
            role@ == RoleView::default(),
    {
        Role {
            inner: deps_hack::k8s_openapi::api::rbac::v1::Role::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
    }


    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures
            self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_policy_rules(&mut self, policy_rules: Vec<PolicyRule>)
        ensures
            self@ == old(self)@.set_policy_rules(policy_rules@.map_values(|policy_rule: PolicyRule| policy_rule@)),
    {
        self.inner.rules = std::option::Option::Some(
            policy_rules.into_iter().map(|p| p.into_kube()).collect()
        )
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::Role {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
        res@.kind == RoleView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::rbac::v1::Role>(&()))
    }

    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<Role, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == RoleView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == RoleView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::rbac::v1::Role>();
        if parse_result.is_ok() {
            let res = Role { inner: parse_result.unwrap() };
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external_body)]
pub struct PolicyRule {
    inner: deps_hack::k8s_openapi::api::rbac::v1::PolicyRule,
}

impl PolicyRule {
    pub spec fn view(&self) -> PolicyRuleView;

    #[verifier(external_body)]
    pub fn default() -> (policy_rule: PolicyRule)
        ensures
            policy_rule@ == PolicyRuleView::default(),
    {
        PolicyRule {
            inner: deps_hack::k8s_openapi::api::rbac::v1::PolicyRule::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_api_groups(&mut self, api_groups: Vec<String>)
        ensures
            self@ == old(self)@.set_api_groups(api_groups@.map_values(|api_group: String| api_group@)),
    {
        self.inner.api_groups = std::option::Option::Some(
            api_groups.into_iter().map(|a: String| a.into_rust_string()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: Vec<String>)
        ensures
            self@ == old(self)@.set_resources(resources@.map_values(|resource: String| resource@)),
    {
        self.inner.resources = std::option::Option::Some(
            resources.into_iter().map(|r: String| r.into_rust_string()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_verbs(&mut self, verbs: Vec<String>)
        ensures
            self@ == old(self)@.set_verbs(verbs@.map_values(|verb: String| verb@)),
    {
        self.inner.verbs = verbs.into_iter().map(|v: String| v.into_rust_string()).collect()
    }


    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::PolicyRule {
        self.inner
    }
}


/// RoleView is the ghost type of Role.
/// It is supposed to be used in spec and proof code.

pub struct RoleView {
    pub metadata: ObjectMetaView,
    pub policy_rules: Option<Seq<PolicyRuleView>>,
}

type RoleSpecView = (Option<Seq<PolicyRuleView>>, ());

impl RoleView {
    pub open spec fn default() -> RoleView {
        RoleView {
            metadata: ObjectMetaView::default(),
            policy_rules: Option::None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> RoleView {
        RoleView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_policy_rules(self, policy_rules: Seq<PolicyRuleView>) -> RoleView {
        RoleView {
            policy_rules: Option::Some(policy_rules),
            ..self
        }
    }

    pub closed spec fn marshal_spec(s: RoleSpecView) -> Value;

    pub closed spec fn unmarshal_spec(v: Value) -> Result<RoleSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    pub proof fn spec_integrity_is_preserved_by_marshal()
        ensures
            forall |s: RoleSpecView|
                Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)).is_Ok()
                && s == Self::unmarshal_spec(Self::marshal_spec(s)).get_Ok_0() {}
}

impl ResourceView for RoleView {
    type Spec = RoleSpecView;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::RoleKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> RoleSpecView {
        (self.policy_rules, ())
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: RoleView::marshal_spec((self.policy_rules, ())),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<RoleView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else if !RoleView::unmarshal_spec(obj.spec).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(RoleView {
                metadata: obj.metadata,
                policy_rules: RoleView::unmarshal_spec(obj.spec).get_Ok_0().0,
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        RoleView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}
}

pub struct PolicyRuleView {
    pub api_groups: Option<Seq<StringView>>,
    pub resources: Option<Seq<StringView>>,
    pub verbs: Seq<StringView>,
}

impl PolicyRuleView {
    pub open spec fn default() -> PolicyRuleView {
        PolicyRuleView {
            api_groups: Option::None,
            resources: Option::None,
            verbs: Seq::empty(),
        }
    }

    pub open spec fn set_api_groups(self, api_groups: Seq<StringView>) -> PolicyRuleView {
        PolicyRuleView {
            api_groups: Option::Some(api_groups),
            ..self
        }
    }

    pub open spec fn set_resources(self, resources: Seq<StringView>) -> PolicyRuleView {
        PolicyRuleView {
            resources: Option::Some(resources),
            ..self
        }
    }

    pub open spec fn set_verbs(self, verbs: Seq<StringView>) -> PolicyRuleView {
        PolicyRuleView {
            verbs: verbs,
            ..self
        }
    }

}

impl Marshalable for PolicyRuleView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
