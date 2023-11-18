// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vstd_ext::{string_map::*, string_view::*};
use crate::zookeeper_controller::trusted::spec_types::ZookeeperClusterView;
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

pub trait Maker {
    spec fn make_headless_service_key(zookeeper: ZookeeperClusterView) -> ObjectRef;
    spec fn make_client_service_key(zookeeper: ZookeeperClusterView) -> ObjectRef;
    spec fn make_admin_server_service_key(zookeeper: ZookeeperClusterView) -> ObjectRef;
    spec fn make_config_map_key(zookeeper: ZookeeperClusterView) -> ObjectRef;
    spec fn make_stateful_set_key(zookeeper: ZookeeperClusterView) -> ObjectRef;

    spec fn make_headless_service(zookeeper: ZookeeperClusterView) -> ServiceView;
    spec fn make_client_service(zookeeper: ZookeeperClusterView) -> ServiceView;
    spec fn make_admin_server_service(zookeeper: ZookeeperClusterView) -> ServiceView;
    spec fn make_config_map(zookeeper: ZookeeperClusterView) -> ConfigMapView;
    spec fn make_stateful_set(zookeeper: ZookeeperClusterView, config_map_rv: StringView) -> StatefulSetView;
}

}
