// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::exec::resource::daemon_set::DaemonSetBuilder;
use crate::fluent_controller::fluentbit::model::resource as model_resource;
use crate::fluent_controller::fluentbit::trusted::{
    exec_types::*, spec_types::FluentBitView, step::*,
};
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ServiceBuilder {}

impl ResourceBuilder<FluentBit, FluentBitReconcileState, model_resource::ServiceBuilder> for ServiceBuilder {
    open spec fn requirements(fb: FluentBitView) -> bool {
        fb.well_formed()
    }

    fn get_request(fb: &FluentBit) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Service::api_resource(),
            name: make_service_name(fb),
            namespace: fb.metadata().namespace().unwrap(),
        }
    }

    fn make(fb: &FluentBit, state: &FluentBitReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_service(fb).marshal())
    }

    fn update(fb: &FluentBit, state: &FluentBitReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            let found_service = service.unwrap();
            if found_service.spec().is_some() {
                return Ok(update_service(fb, found_service).marshal());
            }
        }
        return Err(());
    }

    fn state_after_create(fb: &FluentBit, obj: DynamicObject, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<KubeAPIRequest>), ()>) {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::DaemonSet),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(DaemonSetBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    fn state_after_update(fb: &FluentBit, obj: DynamicObject, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<KubeAPIRequest>), ()>) {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::DaemonSet),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(DaemonSetBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub fn update_service(fb: &FluentBit, found_service: Service) -> (service: Service)
    requires
        fb@.well_formed(),
        found_service@.spec.is_Some(),
    ensures service@ == model_resource::update_service(fb@, found_service@),
{
    let mut service = found_service.clone();
    let made_service = make_service(fb);
    service.set_metadata({
        let mut metadata = found_service.metadata();
        metadata.set_owner_references(make_owner_references(fb));
        metadata.unset_finalizers();
        metadata.set_labels(made_service.metadata().labels().unwrap());
        metadata.set_annotations(made_service.metadata().annotations().unwrap());
        metadata
    });
    service.set_spec({
        let mut spec = found_service.spec().unwrap();
        spec.set_ports(made_service.spec().unwrap().ports().unwrap());
        spec.set_selector(made_service.spec().unwrap().selector().unwrap());

        spec
    });
    service
}

pub fn make_service_name(fb: &FluentBit) -> (name: String)
    requires fb@.well_formed(),
    ensures name@ == model_resource::make_service_name(fb@),
{
    fb.metadata().name().unwrap()
}

pub fn make_service(fb: &FluentBit) -> (service: Service)
    requires fb@.well_formed(),
    ensures service@ == model_resource::make_service(fb@),
{
    let mut service = Service::default();
    service.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_service_name(fb));
        metadata.set_owner_references(make_owner_references(fb));
        metadata.set_labels({
            if fb.spec().service_labels().len() > 0 {
                fb.spec().service_labels()
            } else {
                make_labels(fb)
            }
        });
        metadata.set_annotations(fb.spec().service_annotations());

        metadata
    });
    service.set_spec({
        let mut service_spec = ServiceSpec::default();
        service_spec.set_ports({
            let mut ports = if fb.spec().ports().is_some() {
                    make_new_ports(fb.spec().ports().unwrap())
                } else {
                    Vec::new()
                };
            let mut port = ServicePort::default();
            port.set_name(new_strlit("metrics").to_string());
            if fb.spec().metrics_port().is_some() {
                port.set_port(fb.spec().metrics_port().unwrap());
            } else {
                port.set_port(2020);
            }
            proof {
                assert_seqs_equal!(
                    ports@.map_values(|port: ServicePort| port@).push(port@),
                    model_resource::make_service(fb@).spec.get_Some_0().ports.get_Some_0()
                );
            }
            ports.push(port);
            proof {
                assert_seqs_equal!(
                    ports@.map_values(|port: ServicePort| port@),
                    model_resource::make_service(fb@).spec.get_Some_0().ports.get_Some_0()
                );
            }
            ports
        });
        service_spec.set_selector({
            if fb.spec().service_selector().is_some() {
                fb.spec().service_selector().unwrap()
            } else {
                make_base_labels(fb)
            }
        });
        service_spec
    });
    service
}

fn make_new_ports(ports: Vec<ContainerPort>) -> (service_ports: Vec<ServicePort>)
    ensures service_ports@.map_values(|p: ServicePort| p@) == ports@.map_values(|p: ContainerPort| model_resource::make_service_port(p@)),
{
    let mut service_ports = Vec::new();
    let mut i = 0;
    proof {
        assert_seqs_equal!(
            service_ports@.map_values(|p: ServicePort| p@),
            Seq::new(i as nat, |k: int| model_resource::make_service_port(ports[k]@))
        );
    }
    while i < ports.len()
        invariant
            i <= ports@.len(),
            service_ports@.map_values(|p: ServicePort| p@) == Seq::new(i as nat, |k: int| model_resource::make_service_port(ports[k]@)),
        ensures
            service_ports@.map_values(|p: ServicePort| p@) == Seq::new(ports@.len(), |k: int| model_resource::make_service_port(ports[k]@)),
    {
        let port = &ports[i];
        let mut service_port = ServicePort::default();
        service_port.set_port(port.container_port());
        if port.name().is_some() {
            service_port.set_name(port.name().unwrap());
        }
        if port.protocol().is_some() {
            service_port.set_protocol(port.protocol().unwrap());
        }
        service_ports.push(service_port);
        proof {
            assert(service_port@ == model_resource::make_service_port(port@));
            assert_seqs_equal!(
                service_ports@.map_values(|p: ServicePort| p@),
                Seq::new(i as nat, |k: int| model_resource::make_service_port(ports[k]@)).push(service_port@)
            );
            assert_seqs_equal!(
                Seq::new(i as nat, |k: int| model_resource::make_service_port(ports[k]@)).push(service_port@),
                Seq::new((i + 1) as nat, |k: int| model_resource::make_service_port(ports[k]@))
            );
        }
        i = i + 1;
    }
    proof {
        assert_seqs_equal!(
            ports@.map_values(|p: ContainerPort| model_resource::make_service_port(p@)),
            Seq::new(ports@.len(), |k: int| model_resource::make_service_port(ports[k]@))
        );
    }

    service_ports
}

}
