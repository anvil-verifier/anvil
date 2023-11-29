// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use crate::zookeeper_controller::exec::resource::{
    admin_server_service::AdminServerServiceBuilder, common::*,
};
use crate::zookeeper_controller::model::resource as model_resource;
use crate::zookeeper_controller::trusted::{
    exec_types::*, spec_types::ZookeeperClusterView, step::*,
};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ClientServiceBuilder {}

impl ResourceBuilder<ZookeeperCluster, ZookeeperReconcileState, model_resource::ClientServiceBuilder> for ClientServiceBuilder {
    open spec fn requirements(zk: ZookeeperClusterView) -> bool { zk.well_formed() }

    fn get_request(zk: &ZookeeperCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Service::api_resource(),
            name: make_client_service_name(zk),
            namespace: zk.metadata().namespace().unwrap(),
        }
    }

    fn make(zk: &ZookeeperCluster, state: &ZookeeperReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_client_service(zk).marshal())
    }

    fn update(zk: &ZookeeperCluster, state: &ZookeeperReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            let found_service = service.unwrap();
            if found_service.spec().is_some() {
                return Ok(update_client_service(zk, &found_service).marshal());
            }
        }
        return Err(());
    }

    fn state_after_create(zk: &ZookeeperCluster, obj: DynamicObject, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<KubeAPIRequest>), ()>) {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::AdminServerService),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(AdminServerServiceBuilder::get_request(zk));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    fn state_after_update(zk: &ZookeeperCluster, obj: DynamicObject, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<KubeAPIRequest>), ()>) {
        let service = Service::unmarshal(obj);
        if service.is_ok() {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::AdminServerService),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(AdminServerServiceBuilder::get_request(zk));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub fn make_client_service_name(zk: &ZookeeperCluster) -> (name: String)
    requires zk@.well_formed(),
    ensures name@ == model_resource::make_client_service_name(zk@),
{
    zk.metadata().name().unwrap().concat(new_strlit("-client"))
}

pub fn update_client_service(zk: &ZookeeperCluster, found_client_service: &Service) -> (client_service: Service)
    requires
        zk@.well_formed(),
        found_client_service@.spec.is_Some(),
    ensures client_service@ == model_resource::update_client_service(zk@, found_client_service@),
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
        spec.unset_publish_not_ready_addresses();
        spec
    });
    client_service
}

/// Client Service is used for any client to connect to the zookeeper server
pub fn make_client_service(zk: &ZookeeperCluster) -> (service: Service)
    requires zk@.well_formed(),
    ensures service@ == model_resource::make_client_service(zk@),
{
    let mut ports = Vec::new();

    ports.push(ServicePort::new_with(new_strlit("tcp-client").to_string(), zk.spec().ports().client()));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            model_resource::make_client_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, make_client_service_name(zk), ports, true)
}

}
