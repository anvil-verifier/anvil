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

pub struct HeadlessServiceBuilder {}

impl ResourceBuilder<Service, spec_resource::HeadlessServiceBuilder> for HeadlessServiceBuilder {
    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<Service, RabbitmqError> {
        Ok(make_headless_service(rabbitmq))
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, found_resource: Service) -> Result<Service, RabbitmqError> {
        Ok(update_headless_service(rabbitmq, found_resource))
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

pub fn make_headless_service(rabbitmq: &RabbitmqCluster) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == spec_resource::make_headless_service(rabbitmq@)
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
    make_service(rabbitmq, rabbitmq.name().unwrap().concat(new_strlit("-nodes")), ports, false)
}

}
