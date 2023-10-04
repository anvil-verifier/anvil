// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::resource::service::ServiceBuilder;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::rabbitmq_controller::spec::types::RabbitmqClusterView;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct HeadlessServiceBuilder {}

impl ResourceBuilder<RabbitmqCluster, RabbitmqReconcileState, spec_resource::HeadlessServiceBuilder> for HeadlessServiceBuilder {
    open spec fn requirements(rabbitmq: RabbitmqClusterView) -> bool {
        &&& rabbitmq.metadata.name.is_Some()
        &&& rabbitmq.metadata.namespace.is_Some()
    }

    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Service::api_resource(),
            name: make_headless_service_name(rabbitmq),
            namespace: rabbitmq.namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_headless_service(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            Ok(update_headless_service(rabbitmq, service.unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn state_after_create_or_update(obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, ()>) {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            Ok(state)
        } else {
            Err(())
        }
    }
}

pub fn update_headless_service(rabbitmq: &RabbitmqCluster, found_headless_service: Service) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == spec_resource::update_headless_service(rabbitmq@, found_headless_service@),
{
    let made_service = make_headless_service(rabbitmq);

    let mut headless_service = found_headless_service.clone();
    headless_service.set_spec(made_service.spec().unwrap());
    headless_service.set_metadata({
        let mut metadata = found_headless_service.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_service.metadata().labels().unwrap());
        metadata.set_annotations(made_service.metadata().annotations().unwrap());
        metadata
    });
    headless_service
}

pub fn make_headless_service_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        name@ == spec_resource::make_headless_service_name(rabbitmq@),
{
    rabbitmq.name().unwrap().concat(new_strlit("-nodes"))
}

pub fn make_headless_service(rabbitmq: &RabbitmqCluster) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == spec_resource::make_headless_service(rabbitmq@),
{
    let mut ports = Vec::new();
    ports.push(ServicePort::new_with(new_strlit("epmd").to_string(), 4369));
    ports.push(ServicePort::new_with(new_strlit("cluster-rpc").to_string(), 25672));
    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            spec_resource::make_headless_service(rabbitmq@).spec.get_Some_0().ports.get_Some_0()
        );
    }
    make_service(rabbitmq, make_headless_service_name(rabbitmq), ports, false)
}

}
