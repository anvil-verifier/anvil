// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::model::resource::*;
use crate::fluent_controller::fluentbit::trusted::{
    spec_types::{FluentBitReconcileState, FluentBitView},
    step::*,
};
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::spec::resource_builder::*;
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub open spec fn get_request(sub_resource: SubResource, fb: FluentBitView) -> GetRequest {
    match sub_resource {
        SubResource::ServiceAccount => ServiceAccountBuilder::get_request(fb),
        SubResource::Role => RoleBuilder::get_request(fb),
        SubResource::RoleBinding => RoleBindingBuilder::get_request(fb),
        SubResource::Service => ServiceBuilder::get_request(fb),
        SubResource::DaemonSet => DaemonSetBuilder::get_request(fb),
    }
}

pub open spec fn make(sub_resource: SubResource, fb: FluentBitView, state: FluentBitReconcileState) -> Result<DynamicObjectView, ()> {
    match sub_resource {
        SubResource::ServiceAccount => ServiceAccountBuilder::make(fb, state),
        SubResource::Role => RoleBuilder::make(fb, state),
        SubResource::RoleBinding => RoleBindingBuilder::make(fb, state),
        SubResource::Service => ServiceBuilder::make(fb, state),
        SubResource::DaemonSet => DaemonSetBuilder::make(fb, state),
    }
}

pub open spec fn update(sub_resource: SubResource, fb: FluentBitView, state: FluentBitReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
    match sub_resource {
        SubResource::ServiceAccount => ServiceAccountBuilder::update(fb, state, obj),
        SubResource::Role => RoleBuilder::update(fb, state, obj),
        SubResource::RoleBinding => RoleBindingBuilder::update(fb, state, obj),
        SubResource::Service => ServiceBuilder::update(fb, state, obj),
        SubResource::DaemonSet => DaemonSetBuilder::update(fb, state, obj),
    }
}

pub open spec fn state_after_create(sub_resource: SubResource, fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
    match sub_resource {
        SubResource::ServiceAccount => ServiceAccountBuilder::state_after_create(fb, obj, state),
        SubResource::Role => RoleBuilder::state_after_create(fb, obj, state),
        SubResource::RoleBinding => RoleBindingBuilder::state_after_create(fb, obj, state),
        SubResource::Service => ServiceBuilder::state_after_create(fb, obj, state),
        SubResource::DaemonSet => DaemonSetBuilder::state_after_create(fb, obj, state),
    }
}

pub open spec fn state_after_update(sub_resource: SubResource, fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
    match sub_resource {
        SubResource::ServiceAccount => ServiceAccountBuilder::state_after_update(fb, obj, state),
        SubResource::Role => RoleBuilder::state_after_update(fb, obj, state),
        SubResource::RoleBinding => RoleBindingBuilder::state_after_update(fb, obj, state),
        SubResource::Service => ServiceBuilder::state_after_update(fb, obj, state),
        SubResource::DaemonSet => DaemonSetBuilder::state_after_update(fb, obj, state),
    }
}

pub open spec fn unchangeable(sub_resource: SubResource, object: DynamicObjectView, fb: FluentBitView) -> bool {
    match sub_resource {
        SubResource::ServiceAccount => {
            &&& ServiceAccountView::unmarshal(object).is_Ok()
            &&& ServiceAccountView::unmarshal(object).get_Ok_0().automount_service_account_token == make_service_account(fb).automount_service_account_token
        },
        SubResource::RoleBinding => {
            let rb = RoleBindingView::unmarshal(object).get_Ok_0();
            &&& RoleBindingView::unmarshal(object).is_Ok()
            &&& rb.role_ref == make_role_binding(fb).role_ref
        },
        SubResource::Service => {
            let service = ServiceView::unmarshal(object);
            &&& service.is_Ok()
            &&& service.get_Ok_0().spec.is_Some()
            &&& service.get_Ok_0().spec.get_Some_0().publish_not_ready_addresses.is_None()
        },
        _ => true,
    }
}

}
