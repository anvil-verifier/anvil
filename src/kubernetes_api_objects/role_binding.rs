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
use vstd::string::*;
use vstd::vec::*;

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
            subjects.vec.into_iter().map(|s: Subject| s.into_kube()).collect()
        );
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
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<RoleBinding, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == RoleBindingView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == RoleBindingView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::rbac::v1::RoleBinding>();
        if parse_result.is_ok() {
            let res = RoleBinding { inner: parse_result.unwrap() };
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
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
        self.inner.namespace = std::option::Option::Some(namespace.into_rust_string());
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
            subjects: Option::None,
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
            subjects: Option::Some(subjects),
            ..self
        }
    }

    pub closed spec fn marshal_spec(s: RoleBindingSpecView) -> Value;

    pub closed spec fn unmarshal_spec(v: Value) -> Result<RoleBindingSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    pub proof fn spec_integrity_is_preserved_by_marshal()
        ensures
            forall |s: RoleBindingSpecView|
                Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)).is_Ok()
                && s == Self::unmarshal_spec(Self::marshal_spec(s)).get_Ok_0() {}

}

impl ResourceView for RoleBindingView {
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

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: RoleBindingView::marshal_spec((self.role_ref, self.subjects)),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<RoleBindingView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else if !RoleBindingView::unmarshal_spec(obj.spec).is_Ok() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Result::Ok(RoleBindingView {
                metadata: obj.metadata,
                role_ref: RoleBindingView::unmarshal_spec(obj.spec).get_Ok_0().0,
                subjects: RoleBindingView::unmarshal_spec(obj.spec).get_Ok_0().1,
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        RoleBindingView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}
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
            namespace: Option::None,
        }
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
            namespace: Option::Some(namespace),
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
