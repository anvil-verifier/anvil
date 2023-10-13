// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::exec::types::*;
use crate::zookeeper_controller::spec::resource as spec_resource;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vstd_ext::{string_map::StringMap, string_view::*, to_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub fn make_admin_server_service_name(zk: &ZookeeperCluster) -> (name: String)
    requires
        zk@.well_formed(),
    ensures
        name@ == zk_spec::make_admin_server_service_name(zk@.metadata.name.get_Some_0()),
{
    zk.metadata().name().unwrap().concat(new_strlit("-admin-server"))
}

pub fn update_admin_server_service(zk: &ZookeeperCluster, found_admin_server_service: &Service) -> (admin_server_service: Service)
    requires
        zk@.well_formed(),
        found_admin_server_service@.spec.is_Some(),
    ensures
        admin_server_service@ == zk_spec::update_admin_server_service(zk@, found_admin_server_service@),
{
    let mut admin_server_service = found_admin_server_service.clone();
    let made_admin_server_service = make_admin_server_service(zk);
    admin_server_service.set_metadata({
        let mut metadata = found_admin_server_service.metadata();
        metadata.set_owner_references(make_owner_references(zk));
        metadata.unset_finalizers();
        metadata.set_labels(made_admin_server_service.metadata().labels().unwrap());
        metadata.set_annotations(made_admin_server_service.metadata().annotations().unwrap());
        metadata
    });
    admin_server_service.set_spec({
        let mut spec = found_admin_server_service.spec().unwrap();
        spec.set_ports(made_admin_server_service.spec().unwrap().ports().unwrap());
        spec.set_selector(made_admin_server_service.spec().unwrap().selector().unwrap());
        spec
    });
    admin_server_service
}

/// Admin-server Service is used for client to connect to admin server
pub fn make_admin_server_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.well_formed(),
    ensures
        service@ == zk_spec::make_admin_server_service(zk@),
{
    let mut ports = Vec::new();

    ports.push(ServicePort::new_with(new_strlit("tcp-admin-server").to_string(), zk.spec().ports().admin_server()));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_admin_server_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, make_admin_server_service_name(zk), ports, true)
}

}