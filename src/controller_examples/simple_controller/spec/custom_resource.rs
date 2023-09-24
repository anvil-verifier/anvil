// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::prelude::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

// TODO: SimpleCR should be defined by the controller developer
#[verifier(external_body)]
pub struct SimpleCR {
    inner: deps_hack::SimpleCR
}

impl SimpleCR {
    pub spec fn view(&self) -> SimpleCRView;

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == SimpleCRView::kind(),
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
    pub fn spec(&self) -> (spec: SimpleCRSpec)
        ensures
            spec@ == self@.spec,
    {
        SimpleCRSpec {
            inner: self.inner.spec.clone()
        }
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    fn marshal(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.marshal(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    /// Convert a DynamicObject to a SimpleCR
    // NOTE: This function assumes try_parse won't fail!
    #[verifier(external_body)]
    fn unmarshal(obj: DynamicObject) -> (res: Result<SimpleCR, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == SimpleCRView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == SimpleCRView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::SimpleCR>();
        if parse_result.is_ok() {
            let res = SimpleCR { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

impl ResourceWrapper<deps_hack::SimpleCR> for SimpleCR {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::SimpleCR) -> SimpleCR {
        SimpleCR {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::SimpleCR {
        self.inner
    }
}

pub struct SimpleCRView {
    pub metadata: ObjectMetaView,
    pub spec: SimpleCRSpecView,
    pub status: Option<SimpleCRStatusView>,
}

pub type SimpleCRStatusView = EmptyStatusView;

impl SimpleCRView {
    pub open spec fn well_formed(self) -> bool {
        &&& self.metadata.name.is_Some()
        &&& self.metadata.namespace.is_Some()
        &&& self.metadata.uid.is_Some()
    }

    pub open spec fn controller_owner_ref(self) -> OwnerReferenceView {
        OwnerReferenceView {
            block_owner_deletion: None,
            controller: Some(true),
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            uid: self.metadata.uid.get_Some_0(),
        }
    }
}

impl ResourceView for SimpleCRView {
    type Spec = SimpleCRSpecView;
    type Status = Option<SimpleCRStatusView>;

    open spec fn default() -> SimpleCRView {
        SimpleCRView {
            metadata: ObjectMetaView::default(),
            spec: arbitrary(), // TODO: specify the default value for spec
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::CustomResourceKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> SimpleCRSpecView {
        self.spec
    }

    open spec fn status(self) -> Option<SimpleCRStatusView> {
        self.status
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: SimpleCRView::marshal_spec(self.spec),
            status: SimpleCRView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<SimpleCRView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !SimpleCRView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !SimpleCRView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(SimpleCRView {
                metadata: obj.metadata,
                spec: SimpleCRView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: SimpleCRView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        SimpleCRView::marshal_spec_preserves_integrity();
        SimpleCRView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: SimpleCRSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<SimpleCRSpecView, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<SimpleCRStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<SimpleCRStatusView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        true
    }

    open spec fn transition_validation(self, old_obj: SimpleCRView) -> bool {
        true
    }
}

#[verifier(external_body)]
pub struct SimpleCRSpec {
    inner: deps_hack::SimpleCRSpec
}

pub struct SimpleCRSpecView {
    pub content: StringView,
}

impl SimpleCRSpec {
    pub spec fn view(&self) -> SimpleCRSpecView;

    #[verifier(external_body)]
    pub fn content(&self) -> (content: String)
        ensures
            content@ == self@.content,
    {
        String::from_rust_string(self.inner.content.to_string())
    }
}

impl Marshalable for SimpleCRSpecView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
