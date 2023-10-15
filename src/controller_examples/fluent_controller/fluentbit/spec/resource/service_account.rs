// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::spec::resource::role::RoleBuilder;
use crate::fluent_controller::fluentbit::spec::types::*;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ServiceAccountBuilder {}

impl ResourceBuilder<FluentBitView, FluentBitReconcileState> for ServiceAccountBuilder {
    open spec fn get_request(fb: FluentBitView) -> GetRequest {
        GetRequest { key: make_service_account_key(fb) }
    }

    open spec fn make(fb: FluentBitView, state: FluentBitReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_service_account(fb).marshal())
    }

    open spec fn update(fb: FluentBitView, state: FluentBitReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let sa = ServiceAccountView::unmarshal(obj);
        if sa.is_Ok() {
            Ok(update_service_account(fb, sa.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
        let sa = ServiceAccountView::unmarshal(obj);
        if sa.is_Ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Role),
                ..state
            };
            let req = APIRequest::GetRequest(RoleBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
        let sa = ServiceAccountView::unmarshal(obj);
        if sa.is_Ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Role),
                ..state
            };
            let req = APIRequest::GetRequest(RoleBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn resource_state_matches(fb: FluentBitView, resources: StoredState) -> bool {
        let key = make_service_account_key(fb);
        let obj = resources[key];
        &&& resources.contains_key(key)
        &&& ServiceAccountView::unmarshal(obj).is_Ok()
        &&& ServiceAccountView::unmarshal(obj).get_Ok_0().automount_service_account_token == make_service_account(fb).automount_service_account_token
        &&& obj.metadata.labels == make_service_account(fb).metadata.labels
        &&& obj.metadata.annotations == make_service_account(fb).metadata.annotations
    }

    open spec fn unchangeable(object: DynamicObjectView, fb: FluentBitView) -> bool {
        &&& ServiceAccountView::unmarshal(object).is_Ok()
        &&& ServiceAccountView::unmarshal(object).get_Ok_0().automount_service_account_token == make_service_account(fb).automount_service_account_token
    }
}

pub open spec fn make_service_account_name(fb: FluentBitView) -> StringView
    recommends
        fb.well_formed(),
{
    fb.metadata.name.get_Some_0()
}

pub open spec fn make_service_account_key(fb: FluentBitView) -> ObjectRef
    recommends
        fb.well_formed(),
{
    ObjectRef {
        kind: ServiceAccountView::kind(),
        name: make_service_account_name(fb),
        namespace: fb.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_service_account(fb: FluentBitView, found_service_account: ServiceAccountView) -> ServiceAccountView
    recommends
        fb.well_formed(),
{
    let made_service_account = make_service_account(fb);
    ServiceAccountView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(fb)),
            finalizers: None,
            labels: made_service_account.metadata.labels,
            annotations: made_service_account.metadata.annotations,
            ..found_service_account.metadata
        },
        ..found_service_account
    }
}

pub open spec fn make_service_account(fb: FluentBitView) -> ServiceAccountView
    recommends
        fb.well_formed(),
{
    ServiceAccountView {
        metadata: ObjectMetaView {
            name: Some(make_service_account_name(fb)),
            owner_references: Some(make_owner_references(fb)),
            labels: Some(make_labels(fb)),
            annotations: Some(fb.spec.annotations),
            ..ObjectMetaView::default()
        },
        ..ServiceAccountView::default()
    }
}

}
