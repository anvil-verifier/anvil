// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    spec::{reconciler::*, resource::*, types::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub open spec fn resource_state_matches(
    rabbitmq: RabbitmqClusterView, resource: DynamicObjectView, kind: ResourceKind, resources: Map<ObjectRef, DynamicObjectView>
) -> bool {
    match kind {
        ResourceKind::HeadlessService => {
            let key = HeadlessServiceBuilder::get_request(rabbitmq).key;
            &&& resources.contains_key(key)
            &&& HeadlessServiceBuilder::resource_state_matches(rabbitmq, resources[key])
        },
        ResourceKind::Service => {
            let key = ServiceBuilder::get_request(rabbitmq).key;
            &&& resources.contains_key(key)
            &&& ServiceBuilder::resource_state_matches(rabbitmq, resources[key])
        },
        ResourceKind::ErlangCookieSecret => {
            let key = ErlangCookieBuilder::get_request(rabbitmq).key;
            &&& resources.contains_key(key)
            &&& ErlangCookieBuilder::resource_state_matches(rabbitmq, resources[key])
        },
        ResourceKind::DefaultUserSecret => {
            let key = DefaultUserSecretBuilder::get_request(rabbitmq).key;
            &&& resources.contains_key(key)
            &&& DefaultUserSecretBuilder::resource_state_matches(rabbitmq, resources[key])
        },
        ResourceKind::PluginsConfigMap => {
            let key = PluginsConfigMapBuilder::get_request(rabbitmq).key;
            &&& resources.contains_key(key)
            &&& PluginsConfigMapBuilder::resource_state_matches(rabbitmq, resources[key])
        },
        ResourceKind::ServerConfigMap => {
            let key = ServerConfigMapBuilder::get_request(rabbitmq).key;
            &&& resources.contains_key(key)
            &&& ServerConfigMapBuilder::resource_state_matches(rabbitmq, resources[key])
        },
        ResourceKind::ServiceAccount => {
            let key = ServiceAccountBuilder::get_request(rabbitmq).key;
            &&& resources.contains_key(key)
            &&& ServiceAccountBuilder::resource_state_matches(rabbitmq, resources[key])
        },
        ResourceKind::Role => {
            let key = RoleBuilder::get_request(rabbitmq).key;
            &&& resources.contains_key(key)
            &&& RoleBuilder::resource_state_matches(rabbitmq, resources[key])
        },
        ResourceKind::RoleBinding => {
            let key = RoleBindingBuilder::get_request(rabbitmq).key;
            &&& resources.contains_key(key)
            &&& RoleBindingBuilder::resource_state_matches(rabbitmq, resources[key])
        },
        ResourceKind::StatefulSet => {
            let key = StatefulSetBuilder::get_request(rabbitmq).key;
            &&& resources.contains_key(key)
            &&& StatefulSetBuilder::resource_state_matches(rabbitmq, resources[key])
        },
    }
}

}
