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

pub fn make_client_service_name(zk: &ZookeeperCluster) -> (name: String)
    requires
        zk@.well_formed(),
    ensures
        name@ == zk_spec::make_client_service_name(zk@.metadata.name.get_Some_0()),
{
    zk.metadata().name().unwrap().concat(new_strlit("-client"))
}

pub fn update_client_service(zk: &ZookeeperCluster, found_client_service: &Service) -> (client_service: Service)
    requires
        zk@.well_formed(),
        found_client_service@.spec.is_Some(),
    ensures
        client_service@ == zk_spec::update_client_service(zk@, found_client_service@),
{
    let mut client_service = found_client_service.clone();
    let made_client_service = make_client_service(zk);
    client_service.set_metadata({
        let mut metadata = found_client_service.metadata();
        metadata.set_owner_references(make_owner_references(zk));
        metadata.unset_finalizers();
        metadata.set_labels(made_client_service.metadata().labels().unwrap());
        metadata.set_annotations(made_client_service.metadata().annotations().unwrap());
        metadata
    });
    client_service.set_spec({
        let mut spec = found_client_service.spec().unwrap();
        spec.set_ports(made_client_service.spec().unwrap().ports().unwrap());
        spec.set_selector(made_client_service.spec().unwrap().selector().unwrap());
        spec
    });
    client_service
}

/// Client Service is used for any client to connect to the zookeeper server
pub fn make_client_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.well_formed(),
    ensures
        service@ == zk_spec::make_client_service(zk@),
{
    let mut ports = Vec::new();

    ports.push(ServicePort::new_with(new_strlit("tcp-client").to_string(), zk.spec().ports().client()));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_client_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, make_client_service_name(zk), ports, true)
}

}