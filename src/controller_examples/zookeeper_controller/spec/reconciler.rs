// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_examples::zookeeper_controller::spec::zookeepercluster::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, resource::*, service::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_const::*;
use crate::pervasive_ext::string_view::StringView;
use crate::reconciler::spec::*;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub open spec fn make_headless_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let ports = Seq::empty()
        .push(ServicePortView::default().set_name(new_strlit("tcp-client")@).set_port(2181))
        .push(ServicePortView::default().set_name(new_strlit("tcp-quorum")@).set_port(2888))
        .push(ServicePortView::default().set_name(new_strlit("tcp-leader-election")@).set_port(3888))
        .push(ServicePortView::default().set_name(new_strlit("tcp-metrics")@).set_port(7000))
        .push(ServicePortView::default().set_name(new_strlit("tcp-admin-server")@).set_port(8080));

    make_service(zk, zk.metadata.name.get_Some_0() + new_strlit("-headless")@, ports, false)
}

pub open spec fn make_client_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let ports = Seq::empty().push(ServicePortView::default().set_name(new_strlit("tcp-client")@).set_port(2181));

    make_service(zk, zk.metadata.name.get_Some_0() + new_strlit("-client")@, ports, true)
}

pub open spec fn make_admin_server_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let ports = Seq::empty().push(ServicePortView::default().set_name(new_strlit("tcp-admin-server")@).set_port(8080));

    make_service(zk, zk.metadata.name.get_Some_0() + new_strlit("-admin-server")@, ports, true)
}

pub open spec fn make_service(
    zk: ZookeeperClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool
) -> ServiceView
    recommends
        zk.metadata.name.is_Some(),
        zk.metadata.namespace.is_Some(),
{
    let labels = Map::empty().insert(new_strlit("app")@, zk.metadata.name.get_Some_0());
    let selector = Map::empty().insert(new_strlit("app")@, zk.metadata.name.get_Some_0());
    let service_spec = if !cluster_ip {
        ServiceSpecView::default().set_cluster_ip(new_strlit("None")@).set_ports(ports).set_selector(selector)
    } else {
        ServiceSpecView::default().set_ports(ports).set_selector(selector)
    };
    let service = ServiceView::default()
        .set_name(name)
        .set_namespace(zk.metadata.namespace.get_Some_0())
        .set_labels(labels)
        .set_spec(service_spec);
    service
}

}
