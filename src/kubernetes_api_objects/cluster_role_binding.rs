// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*,
    object_meta::*, resource::*, role_binding::*,
};
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
        ObjectMeta::from_kube(self.inner.metadata.clone())
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
        self.inner.subjects = Some(
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
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<ClusterRoleBinding, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ClusterRoleBindingView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ClusterRoleBindingView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::rbac::v1::ClusterRoleBinding>();
        if parse_result.is_ok() {
            let res = ClusterRoleBinding { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
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
            subjects: None,
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
            subjects: Some(subjects),
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

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ClusterRoleBindingView::marshal_spec((self.role_ref, self.subjects)),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<ClusterRoleBindingView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ClusterRoleBindingView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(ClusterRoleBindingView {
                metadata: obj.metadata,
                role_ref: ClusterRoleBindingView::unmarshal_spec(obj.spec).get_Ok_0().0,
                subjects: ClusterRoleBindingView::unmarshal_spec(obj.spec).get_Ok_0().1,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        ClusterRoleBindingView::marshal_spec_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: ClusterRoleBindingSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<ClusterRoleBindingSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec() {}

    open spec fn state_validation(self) -> bool {
        true
    }

    open spec fn transition_validation(self, old_obj: ClusterRoleBindingView) -> bool {
        true
    }
}

}
