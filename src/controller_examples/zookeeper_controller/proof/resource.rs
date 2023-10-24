// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::spec::resource_builder::*;
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::resource::*;
use crate::zookeeper_controller::spec::types::{ZookeeperClusterView, ZookeeperReconcileState};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub open spec fn get_request(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> GetRequest {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::get_request(zookeeper),
        SubResource::ClientService => ClientServiceBuilder::get_request(zookeeper),
        SubResource::AdminServerService => AdminServerServiceBuilder::get_request(zookeeper),
        SubResource::ConfigMap => ConfigMapBuilder::get_request(zookeeper),
        SubResource::StatefulSet => StatefulSetBuilder::get_request(zookeeper),
    }
}

pub open spec fn make(sub_resource: SubResource, zookeeper: ZookeeperClusterView, state: ZookeeperReconcileState) -> Result<DynamicObjectView, ()> {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::make(zookeeper, state),
        SubResource::ClientService => ClientServiceBuilder::make(zookeeper, state),
        SubResource::AdminServerService => AdminServerServiceBuilder::make(zookeeper, state),
        SubResource::ConfigMap => ConfigMapBuilder::make(zookeeper, state),
        SubResource::StatefulSet => StatefulSetBuilder::make(zookeeper, state),
    }
}

pub open spec fn update(sub_resource: SubResource, zookeeper: ZookeeperClusterView, state: ZookeeperReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::update(zookeeper, state, obj),
        SubResource::ClientService => ClientServiceBuilder::update(zookeeper, state, obj),
        SubResource::AdminServerService => AdminServerServiceBuilder::update(zookeeper, state, obj),
        SubResource::ConfigMap => ConfigMapBuilder::update(zookeeper, state, obj),
        SubResource::StatefulSet => StatefulSetBuilder::update(zookeeper, state, obj),
    }
}

pub open spec fn state_after_create(
    sub_resource: SubResource, zookeeper: ZookeeperClusterView, obj: DynamicObjectView, state: ZookeeperReconcileState
) -> (res: Result<(ZookeeperReconcileState, Option<APIRequest>), ()>) {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::state_after_create(zookeeper, obj, state),
        SubResource::ClientService => ClientServiceBuilder::state_after_create(zookeeper, obj, state),
        SubResource::AdminServerService => AdminServerServiceBuilder::state_after_create(zookeeper, obj, state),
        SubResource::ConfigMap => ConfigMapBuilder::state_after_create(zookeeper, obj, state),
        SubResource::StatefulSet => StatefulSetBuilder::state_after_create(zookeeper, obj, state),
    }
}

pub open spec fn state_after_update(
    sub_resource: SubResource, zookeeper: ZookeeperClusterView, obj: DynamicObjectView, state: ZookeeperReconcileState
) -> (res: Result<(ZookeeperReconcileState, Option<APIRequest>), ()>) {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::state_after_update(zookeeper, obj, state),
        SubResource::ClientService => ClientServiceBuilder::state_after_update(zookeeper, obj, state),
        SubResource::AdminServerService => AdminServerServiceBuilder::state_after_update(zookeeper, obj, state),
        SubResource::ConfigMap => ConfigMapBuilder::state_after_update(zookeeper, obj, state),
        SubResource::StatefulSet => StatefulSetBuilder::state_after_update(zookeeper, obj, state),
    }
}

pub open spec fn unchangeable(sub_resource: SubResource, object: DynamicObjectView, zookeeper: ZookeeperClusterView) -> bool {
    match sub_resource {
        SubResource::HeadlessService => HeadlessServiceBuilder::unchangeable(object, zookeeper),
        SubResource::ClientService => ClientServiceBuilder::unchangeable(object, zookeeper),
        SubResource::AdminServerService => AdminServerServiceBuilder::unchangeable(object, zookeeper),
        SubResource::ConfigMap => ConfigMapBuilder::unchangeable(object, zookeeper),
        SubResource::StatefulSet => StatefulSetBuilder::unchangeable(object, zookeeper),
    }
}

}
