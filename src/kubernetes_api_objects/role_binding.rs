// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*,
    object_meta::*, resource::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {


/// This definition is a wrapper of RoleBinding defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/rbac/v1/role_binding.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/reference/access-authn-authz/rbac/.

#[verifier(external_body)]
pub struct RoleBinding {
    inner: deps_hack::k8s_openapi::api::rbac::v1::RoleBinding,
}

impl RoleBinding {
    pub spec fn view(&self) -> RoleBindingView;

    #[verifier(external_body)]
    pub fn default() -> (role_binding: RoleBinding)
        ensures
            role_binding@ == RoleBindingView::default(),
    {
        RoleBinding {
            inner: deps_hack::k8s_openapi::api::rbac::v1::RoleBinding::default(),
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

    #[verifier(external_body)]
    pub fn clone(&self) -> (c: Self)
        ensures
            c@ == self@,
    {
        RoleBinding { inner: self.inner.clone() }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::RoleBinding {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == RoleBindingView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::rbac::v1::RoleBinding>(&()))
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
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<RoleBinding, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == RoleBindingView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == RoleBindingView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::rbac::v1::RoleBinding>();
        if parse_result.is_ok() {
            let res = RoleBinding { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external_body)]
pub struct RoleRef {
    inner: deps_hack::k8s_openapi::api::rbac::v1::RoleRef,
}

impl RoleRef {
    pub spec fn view(&self) -> RoleRefView;

    #[verifier(external_body)]
    pub fn default() -> (role_ref: RoleRef)
        ensures
            role_ref@ == RoleRefView::default(),
    {
        RoleRef {
            inner: deps_hack::k8s_openapi::api::rbac::v1::RoleRef::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_api_group(&mut self, api_group: String)
        ensures
            self@ == old(self)@.set_api_group(api_group@),
    {
        self.inner.api_group = api_group.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_kind(&mut self, kind: String)
        ensures
            self@ == old(self)@.set_kind(kind@),
    {
        self.inner.kind = kind.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name.into_rust_string();
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::RoleRef {
        self.inner
    }
}

#[verifier(external_body)]
pub struct Subject {
    inner: deps_hack::k8s_openapi::api::rbac::v1::Subject,
}

impl Subject {
    pub spec fn view(&self) -> SubjectView;

    #[verifier(external_body)]
    pub fn default() -> (subject: Subject)
        ensures
            subject@ == SubjectView::default(),
    {
        Subject {
            inner: deps_hack::k8s_openapi::api::rbac::v1::Subject::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_kind(&mut self, kind: String)
        ensures
            self@ == old(self)@.set_kind(kind@),
    {
        self.inner.kind = kind.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures
            self@ == old(self)@.set_namespace(namespace@),
    {
        self.inner.namespace = Some(namespace.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::rbac::v1::Subject {
        self.inner
    }
}

/// RoleBindingView is the ghost type of RoleBinding.
/// It is supposed to be used in spec and proof code.

pub struct RoleBindingView {
    pub metadata: ObjectMetaView,
    pub role_ref: RoleRefView,
    pub subjects: Option<Seq<SubjectView>>,
}

type RoleBindingSpecView = (RoleRefView, Option<Seq<SubjectView>>);

impl RoleBindingView {
    pub open spec fn default() -> RoleBindingView {
        RoleBindingView {
            metadata: ObjectMetaView::default(),
            role_ref: RoleRefView::default(),
            subjects: None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> RoleBindingView {
        RoleBindingView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_role_ref(self, role_ref: RoleRefView) -> RoleBindingView {
        RoleBindingView {
            role_ref: role_ref,
            ..self
        }
    }

    pub open spec fn set_subjects(self, subjects: Seq<SubjectView>) -> RoleBindingView {
        RoleBindingView {
            subjects: Some(subjects),
            ..self
        }
    }
}

impl ResourceView for RoleBindingView {
    type Spec = RoleBindingSpecView;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::RoleBindingKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> RoleBindingSpecView {
        (self.role_ref, self.subjects)
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: RoleBindingView::marshal_spec((self.role_ref, self.subjects)),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<RoleBindingView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !RoleBindingView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(RoleBindingView {
                metadata: obj.metadata,
                role_ref: RoleBindingView::unmarshal_spec(obj.spec).get_Ok_0().0,
                subjects: RoleBindingView::unmarshal_spec(obj.spec).get_Ok_0().1,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        RoleBindingView::marshal_spec_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: RoleBindingSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<RoleBindingSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec() {}

    open spec fn state_validation(self) -> bool {
        &&& self.role_ref.api_group == new_strlit("rbac.authorization.k8s.io")@
        &&& (self.role_ref.kind == new_strlit("Role")@ || self.role_ref.kind == new_strlit("ClusterRole")@)
        &&& self.role_ref.name.len() > 0
        &&& self.subjects.is_Some()
            ==> forall |i| 0 <= i < self.subjects.get_Some_0().len() ==> #[trigger] self.subjects.get_Some_0()[i].state_validation(true)
    }

    open spec fn transition_validation(self, old_obj: RoleBindingView) -> bool {
        &&& old_obj.role_ref == self.role_ref // role_ref is immutable
    }
}

pub struct RoleRefView {
    pub api_group: StringView,
    pub kind: StringView,
    pub name: StringView,
}

impl RoleRefView {
    pub open spec fn default() -> RoleRefView {
        RoleRefView {
            api_group: new_strlit("")@,
            kind: new_strlit("")@,
            name: new_strlit("")@,
        }
    }

    pub open spec fn set_api_group(self, api_group: StringView) -> RoleRefView {
        RoleRefView {
            api_group: api_group,
            ..self
        }
    }

    pub open spec fn set_kind(self, kind: StringView) -> RoleRefView {
        RoleRefView {
            kind: kind,
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> RoleRefView {
        RoleRefView {
            name: name,
            ..self
        }
    }
}

impl Marshalable for RoleRefView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct SubjectView {
    pub kind: StringView,
    pub name: StringView,
    pub namespace: Option<StringView>,
}

impl SubjectView {
    pub open spec fn default() -> SubjectView {
        SubjectView {
            kind: new_strlit("")@,
            name: new_strlit("")@,
            namespace: None,
        }
    }

    pub open spec fn state_validation(self, is_namespaced: bool) -> bool {
        &&& self.kind == new_strlit("ServiceAccount")@ // TODO: support User and Group as kind here
        &&& is_namespaced ==> self.namespace.is_Some() && self.namespace.get_Some_0().len() > 0
    }

    pub open spec fn set_kind(self, kind: StringView) -> SubjectView {
        SubjectView {
            kind: kind,
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> SubjectView {
        SubjectView {
            name: name,
            ..self
        }
    }

    pub open spec fn set_namespace(self, namespace: StringView) -> SubjectView {
        SubjectView {
            namespace: Some(namespace),
            ..self
        }
    }
}

impl Marshalable for SubjectView {
    open spec fn marshal(self) -> Value;

    open spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
