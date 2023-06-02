// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::vec::*;

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
            policy_rules.vec.into_iter().map(|p| p.into_kube()).collect()
        )
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::Role {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::CustomResourceKind,
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
    pub fn from_dynamic_object(obj: DynamicObject) -> (svc: Role)
        ensures
            svc@ == RoleView::from_dynamic_object(obj@),
    {
        Role { inner: obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::rbac::v1::Role>().unwrap() }
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
            api_groups.vec.into_iter().map(|a: String| a.into_rust_string()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: Vec<String>)
        ensures
            self@ == old(self)@.set_resources(resources@.map_values(|resource: String| resource@)),
    {
        self.inner.resources = std::option::Option::Some(
            resources.vec.into_iter().map(|r: String| r.into_rust_string()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_verbs(&mut self, verbs: Vec<String>)
        ensures
            self@ == old(self)@.set_verbs(verbs@.map_values(|verb: String| verb@)),
    {
        self.inner.verbs = verbs.vec.into_iter().map(|v: String| v.into_rust_string()).collect()
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

    pub open spec fn policy_rules_field() -> nat {0}
}

impl ResourceView for RoleView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::RoleKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: self.kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: self.kind(),
            metadata: self.metadata,
            data: Value::Object(Map::empty()
                                    .insert(Self::policy_rules_field(), if self.policy_rules.is_None() {Value::Null} else {
                                    Value::Array(self.policy_rules.get_Some_0().map_values(|v: PolicyRuleView| v.marshal())) // marshal or to dynamic object?
                })
            ),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> RoleView {
        RoleView {
            metadata: obj.metadata,
            policy_rules: if obj.data.get_Object_0()[Self::policy_rules_field()].is_Null() {Option::None} else {
                Option::Some(obj.data.get_Object_0()[Self::policy_rules_field()].get_Array_0().map_values(|v: Value| PolicyRuleView::unmarshal(v)))
            },
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        assert forall |o: Self| o == Self::from_dynamic_object(#[trigger] o.to_dynamic_object()) by {
            if o.policy_rules.is_Some() {
                PolicyRuleView::marshal_preserves_integrity();
                assert_seqs_equal!(
                    o.policy_rules.get_Some_0(),
                    Self::from_dynamic_object(o.to_dynamic_object()).policy_rules.get_Some_0()
                );
            }
        }
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

    pub open spec fn api_groups_field() -> nat {0}

    pub open spec fn resources_field() -> nat {1}

    pub open spec fn verbs_field() -> nat {2}
}

impl Marshalable for PolicyRuleView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::api_groups_field(), if self.api_groups.is_None() {Value::Null} else {
                    Value::Array(self.api_groups.get_Some_0().map_values(|v: StringView| Value::String(v)))
                })
                .insert(Self::resources_field(), if self.resources.is_None() {Value::Null} else {
                    Value::Array(self.resources.get_Some_0().map_values(|v: StringView| Value::String(v)))
                })
                .insert(Self::verbs_field(), Value::Array(self.verbs.map_values(|v: StringView| Value::String(v))))
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        PolicyRuleView {
            api_groups: if value.get_Object_0()[Self::api_groups_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::api_groups_field()].get_Array_0().map_values(|v: Value| v.get_String_0()))
            },
            resources: if value.get_Object_0()[Self::resources_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::resources_field()].get_Array_0().map_values(|v: Value| v.get_String_0()))
            },
            verbs: value.get_Object_0()[Self::verbs_field()].get_Array_0().map_values(|v: Value| v.get_String_0()),
        }
    }

    proof fn marshal_preserves_integrity() {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            if o.api_groups.is_Some() {
                assert_seqs_equal!(
                    o.api_groups.get_Some_0(),
                    Self::unmarshal(o.marshal()).api_groups.get_Some_0()
                );
            }
            if o.resources.is_Some() {
                assert_seqs_equal!(
                    o.resources.get_Some_0(),
                    Self::unmarshal(o.marshal()).resources.get_Some_0()
                );
            }
            assert_seqs_equal!(
                o.verbs,
                Self::unmarshal(o.marshal()).verbs
            );
        }
    }

}

}
