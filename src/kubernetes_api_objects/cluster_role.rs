// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::role::*;
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

/// This definition is a wrapper of ClusterRole defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/rbac/v1/cluster_role.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/reference/access-authn-authz/rbac/.

#[verifier(external_body)]
pub struct ClusterRole {
    inner: deps_hack::k8s_openapi::api::rbac::v1::ClusterRole,
}

impl ClusterRole {
    pub spec fn view(&self) -> ClusterRoleView;

    #[verifier(external_body)]
    pub fn default() -> (cluster_role: ClusterRole)
        ensures
            cluster_role@ == ClusterRoleView::default(),
    {
        ClusterRole {
            inner: deps_hack::k8s_openapi::api::rbac::v1::ClusterRole::default(),
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
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::ClusterRole {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
        res@.kind == ClusterRoleView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::rbac::v1::ClusterRole>(&()))
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
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<ClusterRole, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ClusterRoleView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ClusterRoleView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::rbac::v1::ClusterRole>();
        if parse_result.is_ok() {
            let res = ClusterRole { inner: parse_result.unwrap() };
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
        }
    }
}

/// ClusterRoleView is the ghost type of ClusterRole.
/// It is supposed to be used in spec and proof code.

pub struct ClusterRoleView {
    pub metadata: ObjectMetaView,
    pub policy_rules: Option<Seq<PolicyRuleView>>,
}

type ClusterRoleSpecView = (Option<Seq<PolicyRuleView>>, ());

impl ClusterRoleView {
    pub open spec fn default() -> ClusterRoleView {
        ClusterRoleView {
            metadata: ObjectMetaView::default(),
            policy_rules: Option::None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> ClusterRoleView {
        ClusterRoleView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_policy_rules(self, policy_rules: Seq<PolicyRuleView>) -> ClusterRoleView {
        ClusterRoleView {
            policy_rules: Option::Some(policy_rules),
            ..self
        }
    }

    pub closed spec fn marshal_spec(s: ClusterRoleSpecView) -> Value;

    pub closed spec fn unmarshal_spec(v: Value) -> Result<ClusterRoleSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    pub proof fn spec_integrity_is_preserved_by_marshal()
        ensures
            forall |s: ClusterRoleSpecView|
                Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)).is_Ok()
                && s == Self::unmarshal_spec(Self::marshal_spec(s)).get_Ok_0() {}
}

impl ResourceView for ClusterRoleView {
    type Spec = ClusterRoleSpecView;

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

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ClusterRoleView::marshal_spec((self.policy_rules, ())),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<ClusterRoleView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ClusterRoleView::unmarshal_spec(obj.spec).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(ClusterRoleView {
                metadata: obj.metadata,
                policy_rules: ClusterRoleView::unmarshal_spec(obj.spec).get_Ok_0().0,
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        ClusterRoleView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}

    open spec fn rule(obj: DynamicObjectView) -> bool {
        true
    }

    open spec fn transition_rule(new_cr: DynamicObjectView, old_cr: DynamicObjectView) -> bool {
        true
    }
}

}
