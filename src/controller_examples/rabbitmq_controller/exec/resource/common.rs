// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub trait ResourceBuilder<T: View, SpecBuilder: spec_resource::ResourceBuilder<T::V>> {
    fn get_request(rabbitmq: &RabbitmqCluster) -> (req: KubeGetRequest)
        requires
            rabbitmq@.metadata.name.is_Some(),
            rabbitmq@.metadata.namespace.is_Some(),
        ensures
            req.to_view() == SpecBuilder::get_request(rabbitmq@);

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> (res: Result<DynamicObject, RabbitmqError>)
        requires
            rabbitmq@.metadata.name.is_Some(),
            rabbitmq@.metadata.namespace.is_Some(),
        ensures
            resource_res_to_view(res) == SpecBuilder::make(rabbitmq@, state@);

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, found_resource: T) -> (res: Result<DynamicObject, RabbitmqError>)
        requires
            rabbitmq@.metadata.name.is_Some(),
            rabbitmq@.metadata.namespace.is_Some(),
        ensures
            resource_res_to_view(res) == SpecBuilder::update(rabbitmq@, state@, found_resource@);

    fn get_result_check(obj: DynamicObject) -> (res: Result<T, RabbitmqError>)
        ensures
            resource_res_to_view(res) == SpecBuilder::get_result_check(obj@);

    fn state_after_create_or_update(obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>)
        ensures
            resource_res_to_view(res) == SpecBuilder::state_after_create_or_update(obj@, state@);
}

pub fn make_labels(rabbitmq: &RabbitmqCluster) -> (labels: StringMap)
    requires
        rabbitmq@.metadata.name.is_Some(),
    ensures
        labels@ == spec_resource::make_labels(rabbitmq@),
{
    let mut labels = rabbitmq.spec().labels();
    labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
    labels
}

pub fn make_owner_references(rabbitmq: &RabbitmqCluster) -> (owner_references: Vec<OwnerReference>)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        owner_references@.map_values(|or: OwnerReference| or@) ==  spec_resource::make_owner_references(rabbitmq@),
{
    let mut owner_references = Vec::new();
    owner_references.push(rabbitmq.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
            spec_resource::make_owner_references(rabbitmq@)
        );
    }
    owner_references
}

pub fn make_secret(rabbitmq: &RabbitmqCluster, name:String , data: StringMap) -> (secret: Secret)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        secret@ == spec_resource::make_secret(rabbitmq@, name@, data@)
{
    let mut secret = Secret::default();
    secret.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(name);
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    secret.set_data(data);
    secret
}

pub fn make_service(rabbitmq: &RabbitmqCluster, name:String, ports: Vec<ServicePort>, cluster_ip: bool) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == spec_resource::make_service(rabbitmq@, name@, ports@.map_values(|port: ServicePort| port@), cluster_ip)
{
    let mut service = Service::default();
    service.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(name);
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    service.set_spec({
        let mut service_spec = ServiceSpec::default();
        if !cluster_ip {
            service_spec.set_cluster_ip(new_strlit("None").to_string());
        }
        service_spec.set_ports(ports);
        service_spec.set_selector({
            let mut selector = StringMap::empty();
            selector.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            selector
        });
        service_spec.set_publish_not_ready_addresses(true);
        service_spec
    });
    service
}

}
