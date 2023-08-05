// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::role_binding::*;
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

/// This definition is a wrapper of ClusterRoleBinding defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/rbac/v1/cluster_role_binding.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/reference/access-authn-authz/rbac/.

#[verifier(external_body)]
pub struct ClusterRoleBinding {
    inner: deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding,
}

impl ClusterRoleBinding {
    pub spec fn view(&self) -> ClusterRoleBindingView;

    #[verifier(external_body)]
    pub fn default() -> (role_binding: ClusterRoleBinding)
        ensures
            role_binding@ == ClusterRoleBindingView::default(),
    {
        ClusterRoleBinding {
            inner: deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding::default(),
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
    pub fn set_role_ref(&mut self, role_ref: RoleRef)
        ensures
            self@ == old(self)@.set_role_ref(role_ref@),
    {
        self.inner.role_ref = role_ref.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_subjects(&mut self, subjects: Vec<Subject>)
        ensures
            self@ == old(self)@.set_subjects(subjects@.map_values(|s: Subject| s@)),
    {
        self.inner.subjects = std::option::Option::Some(
            subjects.into_iter().map(|s: Subject| s.into_kube()).collect()
        );
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == ClusterRoleBindingView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding>(&()))
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
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<ClusterRoleBinding, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ClusterRoleBindingView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ClusterRoleBindingView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding>();
        if parse_result.is_ok() {
            let res = ClusterRoleBinding { inner: parse_result.unwrap() };
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
        }
    }
}

/// ClusterRoleBindingView is the ghost type of ClusterRoleBinding.
/// It is supposed to be used in spec and proof code.

pub struct ClusterRoleBindingView {
    pub metadata: ObjectMetaView,
    pub role_ref: RoleRefView,
    pub subjects: Option<Seq<SubjectView>>,
}

type ClusterRoleBindingSpecView = (RoleRefView, Option<Seq<SubjectView>>);

impl ClusterRoleBindingView {
    pub open spec fn default() -> ClusterRoleBindingView {
        ClusterRoleBindingView {
            metadata: ObjectMetaView::default(),
            role_ref: RoleRefView::default(),
            subjects: Option::None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> ClusterRoleBindingView {
        ClusterRoleBindingView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_role_ref(self, role_ref: RoleRefView) -> ClusterRoleBindingView {
        ClusterRoleBindingView {
            role_ref: role_ref,
            ..self
        }
    }

    pub open spec fn set_subjects(self, subjects: Seq<SubjectView>) -> ClusterRoleBindingView {
        ClusterRoleBindingView {
            subjects: Option::Some(subjects),
            ..self
        }
    }

}

impl ResourceView for ClusterRoleBindingView {
    type Spec = ClusterRoleBindingSpecView;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::ClusterRoleBindingKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> ClusterRoleBindingSpecView {
        (self.role_ref, self.subjects)
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ClusterRoleBindingView::marshal_spec((self.role_ref, self.subjects)),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<ClusterRoleBindingView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ClusterRoleBindingView::unmarshal_spec(obj.spec).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(ClusterRoleBindingView {
                metadata: obj.metadata,
                role_ref: ClusterRoleBindingView::unmarshal_spec(obj.spec).get_Ok_0().0,
                subjects: ClusterRoleBindingView::unmarshal_spec(obj.spec).get_Ok_0().1,
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        ClusterRoleBindingView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}

    closed spec fn marshal_spec(s: ClusterRoleBindingSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<ClusterRoleBindingSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn spec_integrity_is_preserved_by_marshal() {}

    open spec fn rule(spec: ClusterRoleBindingSpecView) -> bool {
        true
    }

    open spec fn transition_rule(new_spec: ClusterRoleBindingSpecView, old_spec: ClusterRoleBindingSpecView) -> bool {
        true
    }
}

}
