// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use crate::zookeeper_controller::model::resource::{common::*, config_map::ConfigMapBuilder};
use crate::zookeeper_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct AdminServerServiceBuilder {}

impl ResourceBuilder<ZookeeperClusterView, ZookeeperReconcileState> for AdminServerServiceBuilder {
    open spec fn get_request(zk: ZookeeperClusterView) -> GetRequest {
        GetRequest { key: make_admin_server_service_key(zk) }
    }

    open spec fn make(zk: ZookeeperClusterView, state: ZookeeperReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_admin_server_service(zk).marshal())
    }

    open spec fn update(zk: ZookeeperClusterView, state: ZookeeperReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() && service.get_Ok_0().spec.is_Some() {
            Ok(update_admin_server_service(zk, service.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(zk: ZookeeperClusterView, obj: DynamicObjectView, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<APIRequest>), ()>) {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ConfigMap),
                ..state
            };
            let req = APIRequest::GetRequest(ConfigMapBuilder::get_request(zk));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(zk: ZookeeperClusterView, obj: DynamicObjectView, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<APIRequest>), ()>) {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ConfigMap),
                ..state
            };
            let req = APIRequest::GetRequest(ConfigMapBuilder::get_request(zk));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_admin_server_service_key(zk: ZookeeperClusterView) -> ObjectRef {
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_admin_server_service_name(zk),
        namespace: zk.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn make_admin_server_service_name(zk: ZookeeperClusterView) -> StringView { zk.metadata.name.get_Some_0() + new_strlit("-admin-server")@ }

pub open spec fn update_admin_server_service(zk: ZookeeperClusterView, found_admin_server_service: ServiceView) -> ServiceView {
    ServiceView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(zk)),
            finalizers: None,
            labels: make_admin_server_service(zk).metadata.labels,
            annotations: make_admin_server_service(zk).metadata.annotations,
            ..found_admin_server_service.metadata
        },
        spec: Some(ServiceSpecView {
            ports: make_admin_server_service(zk).spec.get_Some_0().ports,
            selector: make_admin_server_service(zk).spec.get_Some_0().selector,
            publish_not_ready_addresses: make_admin_server_service(zk).spec.get_Some_0().publish_not_ready_addresses,
            ..found_admin_server_service.spec.get_Some_0()
        }),
        ..found_admin_server_service
    }
}

pub open spec fn make_admin_server_service(zk: ZookeeperClusterView) -> ServiceView {
    let ports = seq![ServicePortView::default().set_name(new_strlit("tcp-admin-server")@).set_port(zk.spec.ports.admin_server)];

    make_service(zk, make_admin_server_service_name(zk), ports, true)
}

}
