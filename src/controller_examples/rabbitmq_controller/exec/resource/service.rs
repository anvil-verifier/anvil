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
use crate::rabbitmq_controller::exec::resource::erlang_cookie::ErlangCookieBuilder;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ServiceBuilder {}

impl ResourceBuilder<spec_resource::ServiceBuilder> for ServiceBuilder {
    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Service::api_resource(),
            name: make_main_service_name(rabbitmq),
            namespace: rabbitmq.namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, RabbitmqError> {
        Ok(make_main_service(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, RabbitmqError> {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            Ok(update_main_service(rabbitmq, service.unwrap()).marshal())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    fn state_after_create_or_update(obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            Ok(RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ErlangCookieSecret),
                ..state
            })
        } else {
            Err(RabbitmqError::Error)
        }
    }
}

pub fn update_main_service(rabbitmq: &RabbitmqCluster, found_main_service: Service) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == spec_resource::update_main_service(rabbitmq@, found_main_service@),
{
    let mut main_service = found_main_service.clone();
    let made_service = make_main_service(rabbitmq);
    // TODO: whether to update the ports
    main_service.set_metadata({
        let mut metadata = found_main_service.metadata();
        // The reason why we add these two operations is that it makes the proof easier.
        // In this way, we can easily show that what the owner references and finalizers of the object in every update request
        // for stateful set are.
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_service.metadata().labels().unwrap());
        metadata.set_annotations(made_service.metadata().annotations().unwrap());
        metadata
    });
    main_service
}

pub fn make_main_service_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        name@ == spec_resource::make_main_service_name(rabbitmq@),
{
    rabbitmq.name().unwrap()
}

pub fn make_main_service(rabbitmq: &RabbitmqCluster) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == spec_resource::make_main_service(rabbitmq@)
{
    let mut ports = Vec::new();
    // TODO: check whether the protocols are set to TCP
    ports.push({
        let mut port = ServicePort::new_with(new_strlit("amqp").to_string(), 5672);
        port.set_app_protocol(new_strlit("amqp").to_string());
        port
    });
    ports.push({
        let mut port = ServicePort::new_with(new_strlit("management").to_string(), 15672);
        port.set_app_protocol(new_strlit("http").to_string());
        port
    });
    ports.push({
        let mut port = ServicePort::new_with(new_strlit("prometheus").to_string(), 15692);
        port.set_app_protocol(new_strlit("prometheus.io/metrics").to_string());
        port
    });
    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            spec_resource::make_main_service(rabbitmq@).spec.get_Some_0().ports.get_Some_0()
        );
    }
    make_service(rabbitmq, make_main_service_name(rabbitmq), ports, true)
}

}
