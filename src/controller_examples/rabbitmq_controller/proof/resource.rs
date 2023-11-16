// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::rabbitmq_controller::model::resource::*;
use crate::rabbitmq_controller::trusted::spec_types::{
    RabbitmqClusterView, RabbitmqReconcileState,
};
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::resource_builder::*;
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub open spec fn get_request(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> GetRequest {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::get_request(rabbitmq),
        SubResource::Service => ServiceBuilder::get_request(rabbitmq),
        SubResource::ErlangCookieSecret => ErlangCookieBuilder::get_request(rabbitmq),
        SubResource::DefaultUserSecret => DefaultUserSecretBuilder::get_request(rabbitmq),
        SubResource::PluginsConfigMap => PluginsConfigMapBuilder::get_request(rabbitmq),
        SubResource::ServerConfigMap => ServerConfigMapBuilder::get_request(rabbitmq),
        SubResource::ServiceAccount => ServiceAccountBuilder::get_request(rabbitmq),
        SubResource::Role => RoleBuilder::get_request(rabbitmq),
        SubResource::RoleBinding => RoleBindingBuilder::get_request(rabbitmq),
        SubResource::StatefulSet => StatefulSetBuilder::get_request(rabbitmq),
    }
}

pub open spec fn make(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::make(rabbitmq, state),
        SubResource::Service => ServiceBuilder::make(rabbitmq, state),
        SubResource::ErlangCookieSecret => ErlangCookieBuilder::make(rabbitmq, state),
        SubResource::DefaultUserSecret => DefaultUserSecretBuilder::make(rabbitmq, state),
        SubResource::PluginsConfigMap => PluginsConfigMapBuilder::make(rabbitmq, state),
        SubResource::ServerConfigMap => ServerConfigMapBuilder::make(rabbitmq, state),
        SubResource::ServiceAccount => ServiceAccountBuilder::make(rabbitmq, state),
        SubResource::Role => RoleBuilder::make(rabbitmq, state),
        SubResource::RoleBinding => RoleBindingBuilder::make(rabbitmq, state),
        SubResource::StatefulSet => StatefulSetBuilder::make(rabbitmq, state),
    }
}

pub open spec fn update(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::update(rabbitmq, state, obj),
        SubResource::Service => ServiceBuilder::update(rabbitmq, state, obj),
        SubResource::ErlangCookieSecret => ErlangCookieBuilder::update(rabbitmq, state, obj),
        SubResource::DefaultUserSecret => DefaultUserSecretBuilder::update(rabbitmq, state, obj),
        SubResource::PluginsConfigMap => PluginsConfigMapBuilder::update(rabbitmq, state, obj),
        SubResource::ServerConfigMap => ServerConfigMapBuilder::update(rabbitmq, state, obj),
        SubResource::ServiceAccount => ServiceAccountBuilder::update(rabbitmq, state, obj),
        SubResource::Role => RoleBuilder::update(rabbitmq, state, obj),
        SubResource::RoleBinding => RoleBindingBuilder::update(rabbitmq, state, obj),
        SubResource::StatefulSet => StatefulSetBuilder::update(rabbitmq, state, obj),
    }
}

pub open spec fn state_after_create(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState
) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::state_after_create(rabbitmq, obj, state),
        SubResource::Service => ServiceBuilder::state_after_create(rabbitmq, obj, state),
        SubResource::ErlangCookieSecret => ErlangCookieBuilder::state_after_create(rabbitmq, obj, state),
        SubResource::DefaultUserSecret => DefaultUserSecretBuilder::state_after_create(rabbitmq, obj, state),
        SubResource::PluginsConfigMap => PluginsConfigMapBuilder::state_after_create(rabbitmq, obj, state),
        SubResource::ServerConfigMap => ServerConfigMapBuilder::state_after_create(rabbitmq, obj, state),
        SubResource::ServiceAccount => ServiceAccountBuilder::state_after_create(rabbitmq, obj, state),
        SubResource::Role => RoleBuilder::state_after_create(rabbitmq, obj, state),
        SubResource::RoleBinding => RoleBindingBuilder::state_after_create(rabbitmq, obj, state),
        SubResource::StatefulSet => StatefulSetBuilder::state_after_create(rabbitmq, obj, state),
    }
}

pub open spec fn state_after_update(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState
) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::state_after_update(rabbitmq, obj, state),
        SubResource::Service => ServiceBuilder::state_after_update(rabbitmq, obj, state),
        SubResource::ErlangCookieSecret => ErlangCookieBuilder::state_after_update(rabbitmq, obj, state),
        SubResource::DefaultUserSecret => DefaultUserSecretBuilder::state_after_update(rabbitmq, obj, state),
        SubResource::PluginsConfigMap => PluginsConfigMapBuilder::state_after_update(rabbitmq, obj, state),
        SubResource::ServerConfigMap => ServerConfigMapBuilder::state_after_update(rabbitmq, obj, state),
        SubResource::ServiceAccount => ServiceAccountBuilder::state_after_update(rabbitmq, obj, state),
        SubResource::Role => RoleBuilder::state_after_update(rabbitmq, obj, state),
        SubResource::RoleBinding => RoleBindingBuilder::state_after_update(rabbitmq, obj, state),
        SubResource::StatefulSet => StatefulSetBuilder::state_after_update(rabbitmq, obj, state),
    }
}

pub open spec fn unchangeable(sub_resource: SubResource, object: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> bool {
    match sub_resource {
        SubResource::ErlangCookieSecret => {
            &&& SecretView::unmarshal(object).is_Ok()
            &&& SecretView::unmarshal(object).get_Ok_0().data == make_erlang_secret(rabbitmq).data
        },
        SubResource::ServiceAccount => {
            &&& ServiceAccountView::unmarshal(object).is_Ok()
            &&& ServiceAccountView::unmarshal(object).get_Ok_0().automount_service_account_token == make_service_account(rabbitmq).automount_service_account_token
        },
        SubResource::RoleBinding => {
            let rb = RoleBindingView::unmarshal(object).get_Ok_0();
            &&& RoleBindingView::unmarshal(object).is_Ok()
            &&& rb.role_ref == make_role_binding(rabbitmq).role_ref
        },
        _ => true,
    }
}

}
