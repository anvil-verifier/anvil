// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::resource::*;
use crate::rabbitmq_controller::spec::types::{RabbitmqClusterView, RabbitmqReconcileState};
use crate::reconciler::exec::{io::*, reconciler::*};
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

pub open spec fn make(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, RabbitmqError> {
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

pub open spec fn update(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, RabbitmqError> {
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

pub open spec fn state_after_create_or_update(sub_resource: SubResource, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::state_after_create_or_update(obj, state),
        SubResource::Service => ServiceBuilder::state_after_create_or_update(obj, state),
        SubResource::ErlangCookieSecret => ErlangCookieBuilder::state_after_create_or_update(obj, state),
        SubResource::DefaultUserSecret => DefaultUserSecretBuilder::state_after_create_or_update(obj, state),
        SubResource::PluginsConfigMap => PluginsConfigMapBuilder::state_after_create_or_update(obj, state),
        SubResource::ServerConfigMap => ServerConfigMapBuilder::state_after_create_or_update(obj, state),
        SubResource::ServiceAccount => ServiceAccountBuilder::state_after_create_or_update(obj, state),
        SubResource::Role => RoleBuilder::state_after_create_or_update(obj, state),
        SubResource::RoleBinding => RoleBindingBuilder::state_after_create_or_update(obj, state),
        SubResource::StatefulSet => StatefulSetBuilder::state_after_create_or_update(obj, state),
    }
}

pub open spec fn resource_state_matches(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, obj: DynamicObjectView) -> bool {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::resource_state_matches(rabbitmq, obj),
        SubResource::Service => ServiceBuilder::resource_state_matches(rabbitmq, obj),
        SubResource::ErlangCookieSecret => ErlangCookieBuilder::resource_state_matches(rabbitmq, obj),
        SubResource::DefaultUserSecret => DefaultUserSecretBuilder::resource_state_matches(rabbitmq, obj),
        SubResource::PluginsConfigMap => PluginsConfigMapBuilder::resource_state_matches(rabbitmq, obj),
        SubResource::ServerConfigMap => ServerConfigMapBuilder::resource_state_matches(rabbitmq, obj),
        SubResource::ServiceAccount => ServiceAccountBuilder::resource_state_matches(rabbitmq, obj),
        SubResource::Role => RoleBuilder::resource_state_matches(rabbitmq, obj),
        SubResource::RoleBinding => RoleBindingBuilder::resource_state_matches(rabbitmq, obj),
        SubResource::StatefulSet => StatefulSetBuilder::resource_state_matches(rabbitmq, obj),
    }
}

}
