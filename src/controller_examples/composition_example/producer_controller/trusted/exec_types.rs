// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, label_selector::*, pod_template_spec::*, prelude::*,
};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::producer_controller::trusted::{spec_types, step::*};
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

/// ProducerReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct ProducerReconcileState {
    pub reconcile_step: ProducerReconcileStep,
}

impl View for ProducerReconcileState {
    type V = spec_types::ProducerReconcileState;

    open spec fn view(&self) -> spec_types::ProducerReconcileState {
        spec_types::ProducerReconcileState {
            reconcile_step: self.reconcile_step@,
        }
    }
}

#[verifier(external_body)]
pub struct Producer {
    inner: deps_hack::Producer
}

impl View for Producer {
    type V = spec_types::ProducerView;

    spec fn view(&self) -> spec_types::ProducerView;
}

impl Producer {
    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: ProducerSpec)
        ensures spec@ == self@.spec,
    {
        ProducerSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == spec_types::ProducerView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::Producer>(&()))
    }

    #[verifier(external_body)]
    pub fn controller_owner_ref(&self) -> (owner_reference: OwnerReference)
        ensures owner_reference@ == self@.controller_owner_ref(),
    {
        // We can safely unwrap here because the trait method implementation always returns a Some(...)
        OwnerReference::from_kube(self.inner.controller_owner_ref(&()).unwrap())
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        // TODO: this might be unnecessarily slow
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<Producer, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == spec_types::ProducerView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == spec_types::ProducerView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::Producer>();
        if parse_result.is_ok() {
            let res = Producer { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::Producer> for Producer {
    fn from_kube(inner: deps_hack::Producer) -> Producer { Producer { inner: inner } }

    fn into_kube(self) -> deps_hack::Producer { self.inner }
}

#[verifier(external_body)]
pub struct ProducerSpec {
    inner: deps_hack::ProducerSpec,
}

impl ProducerSpec {
    pub spec fn view(&self) -> spec_types::ProducerSpecView;

    #[verifier(external_body)]
    pub fn message(&self) -> (message: String)
        ensures
            message@ == self@.message,
    {
        self.inner.message.clone()
    }
}

}
