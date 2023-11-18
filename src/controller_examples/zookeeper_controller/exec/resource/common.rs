// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use crate::zookeeper_controller::model::resource as model_resource;
use crate::zookeeper_controller::trusted::{
    exec_types::*, spec_types::ZookeeperClusterView, step::*,
};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub fn make_base_labels(zk: &ZookeeperCluster) -> (labels: StringMap)
    requires zk@.well_formed(),
    ensures labels@ == model_resource::make_base_labels(zk@),
{
    let mut labels = StringMap::empty();
    labels.insert(new_strlit("app").to_string(), zk.metadata().name().unwrap());
    labels
}

pub fn make_labels(zk: &ZookeeperCluster) -> (labels: StringMap)
    requires zk@.well_formed(),
    ensures labels@ == model_resource::make_labels(zk@),
{
    let mut labels = zk.spec().labels();
    labels.extend(make_base_labels(zk));
    labels
}

pub fn make_owner_references(zk: &ZookeeperCluster) -> (owner_references: Vec<OwnerReference>)
    requires zk@.well_formed(),
    ensures owner_references@.map_values(|or: OwnerReference| or@) == model_resource::make_owner_references(zk@),
{
    let mut owner_references = Vec::new();
    owner_references.push(zk.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
            model_resource::make_owner_references(zk@)
        );
    }
    owner_references
}

/// make_service constructs the Service object given the name, ports and cluster_ip
pub fn make_service(zk: &ZookeeperCluster, name: String, ports: Vec<ServicePort>, cluster_ip: bool) -> (service: Service)
    requires zk@.well_formed(),
    ensures service@ == model_resource::make_service(zk@, name@, ports@.map_values(|port: ServicePort| port@), cluster_ip),
{
    let mut service = Service::default();
    service.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(name);
        metadata.set_labels(make_labels(zk));
        metadata.set_annotations(zk.spec().annotations());
        metadata.set_owner_references(make_owner_references(zk));
        metadata
    });
    service.set_spec({
        let mut service_spec = ServiceSpec::default();
        if !cluster_ip {
            service_spec.set_cluster_ip(new_strlit("None").to_string());
        }
        service_spec.set_ports(ports);
        service_spec.set_selector(make_base_labels(zk));
        service_spec
    });

    service
}

}
