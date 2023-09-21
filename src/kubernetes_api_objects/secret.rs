// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*,
    object_meta::*, resource::*,
};
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {

/// Secret is a type of API object used to store confidential data in key-value pairs.
/// A Secret object can be used to set environment variables or configuration files
/// in a Volume mounted to a Pod.
///
/// This definition is a wrapper of Secret defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/secret.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/configuration/secret/.

#[verifier(external_body)]
pub struct Secret {
    inner: deps_hack::k8s_openapi::api::core::v1::Secret,
}

impl Secret {
    pub spec fn view(&self) -> SecretView;

    #[verifier(external_body)]
    pub fn default() -> (secret: Secret)
        ensures
            secret@ == SecretView::default(),
    {
        Secret {
            inner: deps_hack::k8s_openapi::api::core::v1::Secret::default(),
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
    pub fn data(&self) -> (data: Option<StringMap>)
        ensures
            self@.data.is_Some() == data.is_Some(),
            data.is_Some() ==> data.get_Some_0()@ == self@.data.get_Some_0(),
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

    // @TODO: data is a map of string to bytestring. May support it in the future.
    #[verifier(external_body)]
    pub fn set_data(&mut self, data: StringMap)
        ensures
            self@ == old(self)@.set_data(data@),
    {
        let string_map = data.into_rust_map();
        let mut binary_map: std::collections::BTreeMap<std::string::String, deps_hack::k8s_openapi::ByteString> = std::collections::BTreeMap::new();
        for (key, value) in string_map {
            binary_map.insert(key, deps_hack::k8s_openapi::ByteString(value.into_bytes()));
        }
        self.inner.data = Some(binary_map)
    }

    #[verifier(external_body)]
    pub fn set_type(&mut self, type_: String)
        ensures
            self@ == old(self)@.set_type(type_@),
    {
        self.inner.type_ = Some(type_.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (c: Self)
        ensures
            c@ == self@,
    {
        Secret { inner: self.inner.clone() }
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Secret) -> Secret {
        Secret {
            inner: inner
        }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Secret {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == SecretView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::Secret>(&()))
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
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<Secret, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == SecretView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == SecretView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::Secret>();
        if parse_result.is_ok() {
            let res = Secret { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

/// SecretView is the ghost type of Secret.
/// It is supposed to be used in spec and proof code.

pub struct SecretView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>, // For view, <String, String> map is used instead of <String, Bytestring> map for now.
    pub type_: Option<StringView>,
}

type SecretSpecView = (Option<Map<StringView, StringView>>, Option<StringView>);

impl SecretView {
    pub open spec fn default() -> SecretView {
        SecretView {
            metadata: ObjectMetaView::default(),
            data: None,
            type_: None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> SecretView {
        SecretView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_data(self, data: Map<StringView, StringView>) -> SecretView {
        SecretView {
            data: Some(data),
            ..self
        }
    }

    pub open spec fn set_type(self, type_: StringView) -> SecretView {
        SecretView {
            type_: Some(type_),
            ..self
        }
    }
}

impl ResourceView for SecretView {
    type Spec = SecretSpecView;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::SecretKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    open spec fn spec(self) -> SecretSpecView {
        (self.data, self.type_)
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: SecretView::marshal_spec((self.data, self.type_)),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<SecretView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !SecretView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(SecretView {
                metadata: obj.metadata,
                data: SecretView::unmarshal_spec(obj.spec).get_Ok_0().0,
                type_: SecretView::unmarshal_spec(obj.spec).get_Ok_0().1,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        SecretView::marshal_spec_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    open spec fn marshal_spec(s: SecretSpecView) -> Value;

    open spec fn unmarshal_spec(v: Value) -> Result<SecretSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec() {}

    open spec fn state_validation(self) -> bool {
        true
    }

    open spec fn transition_validation(self, old_obj: SecretView) -> bool {
        true
    }
}

}
