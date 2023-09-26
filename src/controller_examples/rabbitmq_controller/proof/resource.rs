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

pub open spec fn get_request(kind: ResourceKind, rabbitmq: RabbitmqClusterView) -> GetRequest {
    match kind {
        ResourceKind::HeadlessService => HeadlessServiceBuilder::get_request(rabbitmq),
        ResourceKind::Service => ServiceBuilder::get_request(rabbitmq),
        ResourceKind::ErlangCookieSecret => ErlangCookieBuilder::get_request(rabbitmq),
        ResourceKind::DefaultUserSecret => DefaultUserSecretBuilder::get_request(rabbitmq),
        ResourceKind::PluginsConfigMap => PluginsConfigMapBuilder::get_request(rabbitmq),
        ResourceKind::ServerConfigMap => ServerConfigMapBuilder::get_request(rabbitmq),
        ResourceKind::ServiceAccount => ServiceAccountBuilder::get_request(rabbitmq),
        ResourceKind::Role => RoleBuilder::get_request(rabbitmq),
        ResourceKind::RoleBinding => RoleBindingBuilder::get_request(rabbitmq),
        ResourceKind::StatefulSet => StatefulSetBuilder::get_request(rabbitmq),
    }
}

pub open spec fn make(kind: ResourceKind, rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, RabbitmqError> {
    match kind {
        ResourceKind::HeadlessService => HeadlessServiceBuilder::make(rabbitmq, state),
        ResourceKind::Service => ServiceBuilder::make(rabbitmq, state),
        ResourceKind::ErlangCookieSecret => ErlangCookieBuilder::make(rabbitmq, state),
        ResourceKind::DefaultUserSecret => DefaultUserSecretBuilder::make(rabbitmq, state),
        ResourceKind::PluginsConfigMap => PluginsConfigMapBuilder::make(rabbitmq, state),
        ResourceKind::ServerConfigMap => ServerConfigMapBuilder::make(rabbitmq, state),
        ResourceKind::ServiceAccount => ServiceAccountBuilder::make(rabbitmq, state),
        ResourceKind::Role => RoleBuilder::make(rabbitmq, state),
        ResourceKind::RoleBinding => RoleBindingBuilder::make(rabbitmq, state),
        ResourceKind::StatefulSet => StatefulSetBuilder::make(rabbitmq, state),
    }
}

pub open spec fn update(kind: ResourceKind, rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, RabbitmqError> {
    match kind {
        ResourceKind::HeadlessService => HeadlessServiceBuilder::update(rabbitmq, state, obj),
        ResourceKind::Service => ServiceBuilder::update(rabbitmq, state, obj),
        ResourceKind::ErlangCookieSecret => ErlangCookieBuilder::update(rabbitmq, state, obj),
        ResourceKind::DefaultUserSecret => DefaultUserSecretBuilder::update(rabbitmq, state, obj),
        ResourceKind::PluginsConfigMap => PluginsConfigMapBuilder::update(rabbitmq, state, obj),
        ResourceKind::ServerConfigMap => ServerConfigMapBuilder::update(rabbitmq, state, obj),
        ResourceKind::ServiceAccount => ServiceAccountBuilder::update(rabbitmq, state, obj),
        ResourceKind::Role => RoleBuilder::update(rabbitmq, state, obj),
        ResourceKind::RoleBinding => RoleBindingBuilder::update(rabbitmq, state, obj),
        ResourceKind::StatefulSet => StatefulSetBuilder::update(rabbitmq, state, obj),
    }
}

pub open spec fn state_after_create_or_update(kind: ResourceKind, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
    match kind {
        ResourceKind::HeadlessService => HeadlessServiceBuilder::state_after_create_or_update(obj, state),
        ResourceKind::Service => ServiceBuilder::state_after_create_or_update(obj, state),
        ResourceKind::ErlangCookieSecret => ErlangCookieBuilder::state_after_create_or_update(obj, state),
        ResourceKind::DefaultUserSecret => DefaultUserSecretBuilder::state_after_create_or_update(obj, state),
        ResourceKind::PluginsConfigMap => PluginsConfigMapBuilder::state_after_create_or_update(obj, state),
        ResourceKind::ServerConfigMap => ServerConfigMapBuilder::state_after_create_or_update(obj, state),
        ResourceKind::ServiceAccount => ServiceAccountBuilder::state_after_create_or_update(obj, state),
        ResourceKind::Role => RoleBuilder::state_after_create_or_update(obj, state),
        ResourceKind::RoleBinding => RoleBindingBuilder::state_after_create_or_update(obj, state),
        ResourceKind::StatefulSet => StatefulSetBuilder::state_after_create_or_update(obj, state),
    }
}

pub open spec fn resource_state_matches(kind: ResourceKind, rabbitmq: RabbitmqClusterView, obj: DynamicObjectView) -> bool {
    match kind {
        ResourceKind::HeadlessService => HeadlessServiceBuilder::resource_state_matches(rabbitmq, obj),
        ResourceKind::Service => ServiceBuilder::resource_state_matches(rabbitmq, obj),
        ResourceKind::ErlangCookieSecret => ErlangCookieBuilder::resource_state_matches(rabbitmq, obj),
        ResourceKind::DefaultUserSecret => DefaultUserSecretBuilder::resource_state_matches(rabbitmq, obj),
        ResourceKind::PluginsConfigMap => PluginsConfigMapBuilder::resource_state_matches(rabbitmq, obj),
        ResourceKind::ServerConfigMap => ServerConfigMapBuilder::resource_state_matches(rabbitmq, obj),
        ResourceKind::ServiceAccount => ServiceAccountBuilder::resource_state_matches(rabbitmq, obj),
        ResourceKind::Role => RoleBuilder::resource_state_matches(rabbitmq, obj),
        ResourceKind::RoleBinding => RoleBindingBuilder::resource_state_matches(rabbitmq, obj),
        ResourceKind::StatefulSet => StatefulSetBuilder::resource_state_matches(rabbitmq, obj),
    }
}

}
