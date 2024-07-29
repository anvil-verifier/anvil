// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::consumer_controller::trusted::{spec_types, step::*};
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, label_selector::*, pod_template_spec::*, prelude::*,
};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

/// ConsumerReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct ConsumerReconcileState {
    pub reconcile_step: ConsumerReconcileStep,
}

impl View for ConsumerReconcileState {
    type V = spec_types::ConsumerReconcileState;

    open spec fn view(&self) -> spec_types::ConsumerReconcileState {
        spec_types::ConsumerReconcileState {
            reconcile_step: self.reconcile_step@,
        }
    }
}

#[verifier(external_body)]
pub struct Consumer {
    inner: deps_hack::Consumer
}

impl View for Consumer {
    type V = spec_types::ConsumerView;

    spec fn view(&self) -> spec_types::ConsumerView;
}

impl Consumer {
    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: ConsumerSpec)
        ensures spec@ == self@.spec,
    {
        ConsumerSpec { inner: self.inner.spec.clone() }
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == spec_types::ConsumerView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::Consumer>(&()))
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
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<Consumer, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == spec_types::ConsumerView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == spec_types::ConsumerView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::Consumer>();
        if parse_result.is_ok() {
            let res = Consumer { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::Consumer> for Consumer {
    fn from_kube(inner: deps_hack::Consumer) -> Consumer { Consumer { inner: inner } }

    fn into_kube(self) -> deps_hack::Consumer { self.inner }
}

#[verifier(external_body)]
pub struct ConsumerSpec {
    inner: deps_hack::ConsumerSpec,
}

impl ConsumerSpec {
    pub spec fn view(&self) -> spec_types::ConsumerSpecView;

    #[verifier(external_body)]
    pub fn message(&self) -> (message: String)
        ensures
            message@ == self@.message,
    {
        self.inner.message.clone()
    }
}

}
