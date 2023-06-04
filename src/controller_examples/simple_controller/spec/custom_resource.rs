// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

// TODO: CustomResource should be defined by the controller developer
#[verifier(external_body)]
pub struct CustomResource {
    inner: deps_hack::SimpleCR
}

pub struct CustomResourceView {
    pub metadata: ObjectMetaView,
    pub spec: CustomResourceSpecView,
}

impl CustomResource {
    pub spec fn view(&self) -> CustomResourceView;

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::CustomResourceKind,
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::SimpleCR>(&()))
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: CustomResourceSpec)
        ensures
            spec@ == self@.spec,
    {
        CustomResourceSpec {
            inner: self.inner.spec.clone()
        }
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    /// Convert a DynamicObject to a CustomResource
    // NOTE: This function assumes try_parse won't fail!
    #[verifier(external_body)]
    fn from_dynamic_object(obj: DynamicObject) -> (res: Result<CustomResource, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == CustomResourceView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == CustomResourceView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::SimpleCR>();
        if parse_result.is_ok() {
            let res = CustomResource { inner: parse_result.unwrap() };
            Result::Ok(res)
        } else {
            Result::Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::SimpleCR> for CustomResource {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::SimpleCR) -> CustomResource {
        CustomResource {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::SimpleCR {
        self.inner
    }
}

impl CustomResourceView {}

impl ResourceView for CustomResourceView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::CustomResourceKind
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
            data: Value::Object(Map::empty().insert(spec_field(), self.spec.marshal())),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<CustomResourceView, ParseDynamicObjectError> {
        let data_object = obj.data.get_Object_0();
        let data_spec_unmarshal = CustomResourceSpecView::unmarshal(data_object[spec_field()]);
        if !obj.data.is_Object() {
            Result::Err(ParseDynamicObjectError::UnexpectedType)
        } else if !data_object.dom().contains(spec_field()) {
            Result::Err(ParseDynamicObjectError::MissingField)
        } else if data_spec_unmarshal.is_Err() {
            Result::Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            let res = CustomResourceView {
                metadata: obj.metadata,
                spec: data_spec_unmarshal.get_Ok_0(),
            };
            Result::Ok(res)
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        CustomResourceSpecView::marshal_preserves_integrity();
        CustomResourceSpecView::marshal_returns_non_null();
    }
}

#[verifier(external_body)]
pub struct CustomResourceSpec {
    inner: deps_hack::SimpleCRSpec
}

pub struct CustomResourceSpecView {
    pub content: StringView,
}

impl CustomResourceSpec {
    pub spec fn view(&self) -> CustomResourceSpecView;

    #[verifier(external_body)]
    pub fn content(&self) -> (content: String)
        ensures
            content@ == self@.content,
    {
        String::from_rust_string(self.inner.content.to_string())
    }
}

impl Marshalable for CustomResourceSpecView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}


pub open spec fn spec_field() -> nat {0}

pub open spec fn spec_content_field() -> nat {0}

}
