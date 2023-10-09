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

pub open spec fn get_key(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> ObjectRef {
    match sub_resource {
        SubResource::HeadlessService => make_headless_service_key(rabbitmq),
        SubResource::Service => make_main_service_key(rabbitmq),
        SubResource::ErlangCookieSecret => make_erlang_secret_key(rabbitmq),
        SubResource::DefaultUserSecret => make_default_user_secret_key(rabbitmq),
        SubResource::PluginsConfigMap => make_plugins_config_map_key(rabbitmq),
        SubResource::ServerConfigMap => make_server_config_map_key(rabbitmq),
        SubResource::ServiceAccount => make_service_account_key(rabbitmq),
        SubResource::Role => make_role_key(rabbitmq),
        SubResource::RoleBinding => make_role_binding_key(rabbitmq),
        SubResource::StatefulSet => make_stateful_set_key(rabbitmq),
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

pub open spec fn state_after_create_or_update(sub_resource: SubResource, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, ()>) {
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

pub open spec fn resource_state_matches(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resources: StoredState) -> bool {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::resource_state_matches(rabbitmq, resources),
        SubResource::Service => ServiceBuilder::resource_state_matches(rabbitmq, resources),
        SubResource::ErlangCookieSecret => ErlangCookieBuilder::resource_state_matches(rabbitmq, resources),
        SubResource::DefaultUserSecret => DefaultUserSecretBuilder::resource_state_matches(rabbitmq, resources),
        SubResource::PluginsConfigMap => PluginsConfigMapBuilder::resource_state_matches(rabbitmq, resources),
        SubResource::ServerConfigMap => ServerConfigMapBuilder::resource_state_matches(rabbitmq, resources),
        SubResource::ServiceAccount => ServiceAccountBuilder::resource_state_matches(rabbitmq, resources),
        SubResource::Role => RoleBuilder::resource_state_matches(rabbitmq, resources),
        SubResource::RoleBinding => RoleBindingBuilder::resource_state_matches(rabbitmq, resources),
        SubResource::StatefulSet => StatefulSetBuilder::resource_state_matches(rabbitmq, resources),
    }
}

pub open spec fn unchangeable(sub_resource: SubResource, object: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> bool {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::unchangeable(object, rabbitmq),
        SubResource::Service => ServiceBuilder::unchangeable(object, rabbitmq),
        SubResource::ErlangCookieSecret => ErlangCookieBuilder::unchangeable(object, rabbitmq),
        SubResource::DefaultUserSecret => DefaultUserSecretBuilder::unchangeable(object, rabbitmq),
        SubResource::PluginsConfigMap => PluginsConfigMapBuilder::unchangeable(object, rabbitmq),
        SubResource::ServerConfigMap => ServerConfigMapBuilder::unchangeable(object, rabbitmq),
        SubResource::ServiceAccount => ServiceAccountBuilder::unchangeable(object, rabbitmq),
        SubResource::Role => RoleBuilder::unchangeable(object, rabbitmq),
        SubResource::RoleBinding => RoleBindingBuilder::unchangeable(object, rabbitmq),
        SubResource::StatefulSet => StatefulSetBuilder::unchangeable(object, rabbitmq),
    }
}

}
