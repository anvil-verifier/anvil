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

/// A service account is a type of non-human account that, in Kubernetes, provides a distinct identity in a Kubernetes cluster.
/// Application Pods, system components, and entities inside and outside the cluster can use a specific ServiceAccount's credentials to identify as that ServiceAccount.
/// This identity is useful in various situations, including authenticating to the API server or implementing identity-based security policies.
///
/// This definition is a wrapper of ServiceAccount defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/service_account.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/security/service-accounts/.

#[verifier(external_body)]
pub struct ServiceAccount {
    inner: deps_hack::k8s_openapi::api::core::v1::ServiceAccount,
}

impl ServiceAccount {
    pub spec fn view(&self) -> ServiceAccountView;

    #[verifier(external_body)]
    pub fn default() -> (service_account: ServiceAccount)
        ensures
            service_account@ == ServiceAccountView::default(),
    {
        ServiceAccount {
            inner: deps_hack::k8s_openapi::api::core::v1::ServiceAccount::default(),
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
    pub fn clone(&self) -> (c: Self)
        ensures
            c@ == self@,
    {
        ServiceAccount { inner: self.inner.clone() }
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ServiceAccount) -> ServiceAccount {
        ServiceAccount {
            inner: inner
        }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ServiceAccount {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == ServiceAccountView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::ServiceAccount>(&()))
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
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<ServiceAccount, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ServiceAccountView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ServiceAccountView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::ServiceAccount>();
        if parse_result.is_ok() {
            let res = ServiceAccount { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

/// ServiceAccountView is the ghost type of ServiceAccount.
/// It is supposed to be used in spec and proof code.

pub struct ServiceAccountView {
    pub metadata: ObjectMetaView,
    pub automount_service_account_token: Option<bool>,
}
type ServiceAccountSpecView = (Option<bool>, ());

impl ServiceAccountView {
    pub open spec fn default() -> ServiceAccountView {
        ServiceAccountView {
            metadata: ObjectMetaView::default(),
            automount_service_account_token: None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> ServiceAccountView {
        ServiceAccountView {
            metadata: metadata,
            ..self
        }
    }
}

impl ResourceView for ServiceAccountView {
    type Spec = ServiceAccountSpecView;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::ServiceAccountKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> ServiceAccountSpecView {
        (self.automount_service_account_token, ())
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ServiceAccountView::marshal_spec((self.automount_service_account_token, ())),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<ServiceAccountView, ParseDynamicObjectError> {
            if obj.kind != Self::kind() {
                Err(ParseDynamicObjectError::UnmarshalError)
            } else if !ServiceAccountView::unmarshal_spec(obj.spec).is_Ok() {
                Err(ParseDynamicObjectError::UnmarshalError)
            } else {
                Ok(ServiceAccountView {
                    metadata: obj.metadata,
                    automount_service_account_token: ServiceAccountView::unmarshal_spec(obj.spec).get_Ok_0().0,
                })
            }
    }

    proof fn marshal_preserves_integrity() {
        ServiceAccountView::marshal_spec_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: ServiceAccountSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<ServiceAccountSpecView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec() {}

    open spec fn state_validation(self) -> bool {
        true
    }

    open spec fn transition_validation(self, old_obj: ServiceAccountView) -> bool {
        true
    }
}

}
