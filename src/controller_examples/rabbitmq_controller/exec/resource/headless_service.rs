// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::rabbitmq_controller::exec::resource::service::ServiceBuilder;
use crate::rabbitmq_controller::model::resource as model_resource;
use crate::rabbitmq_controller::trusted::exec_types::*;
use crate::rabbitmq_controller::trusted::spec_types::RabbitmqClusterView;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct HeadlessServiceBuilder {}

impl ResourceBuilder<RabbitmqCluster, RabbitmqReconcileState, model_resource::HeadlessServiceBuilder> for HeadlessServiceBuilder {
    open spec fn requirements(rabbitmq: RabbitmqClusterView) -> bool { rabbitmq.well_formed() }

    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Service::api_resource(),
            name: make_headless_service_name(rabbitmq),
            namespace: rabbitmq.metadata().namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_headless_service(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            let found_service = service.unwrap();
            if found_service.spec().is_some() {
                return Ok(update_headless_service(rabbitmq, found_service).marshal());
            }
        }
        Err(())
    }

    fn state_after_create(rabbitmq: &RabbitmqCluster, obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<KubeAPIRequest>), ()>) {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Service),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(ServiceBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    fn state_after_update(rabbitmq: &RabbitmqCluster, obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<KubeAPIRequest>), ()>) {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Service),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(ServiceBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub fn update_headless_service(rabbitmq: &RabbitmqCluster, found_headless_service: Service) -> (service: Service)
    requires
        rabbitmq@.well_formed(),
        found_headless_service@.spec.is_Some(),
    ensures service@ == model_resource::update_headless_service(rabbitmq@, found_headless_service@),
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
    headless_service.set_spec({
        let mut svc_spec = found_headless_service.spec().unwrap();
        let made_spec = made_service.spec().unwrap();
        svc_spec.set_ports(made_spec.ports().unwrap());
        svc_spec.set_selector(made_spec.selector().unwrap());
        svc_spec.set_publish_not_ready_addresses(made_spec.publish_not_ready_addresses().unwrap());
        svc_spec
    });
    headless_service
}

pub fn make_headless_service_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires
        rabbitmq@.well_formed(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        name@ == model_resource::make_headless_service_name(rabbitmq@),
{
    rabbitmq.metadata().name().unwrap().concat(new_strlit("-nodes"))
}

pub fn make_headless_service(rabbitmq: &RabbitmqCluster) -> (service: Service)
    requires rabbitmq@.well_formed(),
    ensures service@ == model_resource::make_headless_service(rabbitmq@),
{
    let mut ports = Vec::new();
    ports.push(ServicePort::new_with(new_strlit("epmd").to_string(), 4369));
    ports.push(ServicePort::new_with(new_strlit("cluster-rpc").to_string(), 25672));
    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            model_resource::make_headless_service(rabbitmq@).spec.get_Some_0().ports.get_Some_0()
        );
    }
    make_service(rabbitmq, make_headless_service_name(rabbitmq), ports, false)
}

}
