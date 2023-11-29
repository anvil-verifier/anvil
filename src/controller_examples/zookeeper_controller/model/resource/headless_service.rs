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
use crate::zookeeper_controller::model::resource::{
    client_service::ClientServiceBuilder, common::*,
};
use crate::zookeeper_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct HeadlessServiceBuilder {}

impl ResourceBuilder<ZookeeperClusterView, ZookeeperReconcileState> for HeadlessServiceBuilder {
    open spec fn get_request(zk: ZookeeperClusterView) -> GetRequest {
        GetRequest { key: make_headless_service_key(zk) }
    }

    open spec fn make(zk: ZookeeperClusterView, state: ZookeeperReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_headless_service(zk).marshal())
    }

    open spec fn update(zk: ZookeeperClusterView, state: ZookeeperReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() && service.get_Ok_0().spec.is_Some() {
            Ok(update_headless_service(zk, service.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(zk: ZookeeperClusterView, obj: DynamicObjectView, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<APIRequest>), ()>) {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ClientService),
                ..state
            };
            let req = APIRequest::GetRequest(ClientServiceBuilder::get_request(zk));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(zk: ZookeeperClusterView, obj: DynamicObjectView, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<APIRequest>), ()>) {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ClientService),
                ..state
            };
            let req = APIRequest::GetRequest(ClientServiceBuilder::get_request(zk));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_headless_service_key(zk: ZookeeperClusterView) -> ObjectRef {
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_headless_service_name(zk),
        namespace: zk.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn make_headless_service_name(zk: ZookeeperClusterView) -> StringView { zk.metadata.name.get_Some_0() + new_strlit("-headless")@ }

pub open spec fn update_headless_service(zk: ZookeeperClusterView, found_headless_service: ServiceView) -> ServiceView {
    ServiceView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(zk)),
            finalizers: None,
            labels: make_headless_service(zk).metadata.labels,
            annotations: make_headless_service(zk).metadata.annotations,
            ..found_headless_service.metadata
        },
        spec: Some(ServiceSpecView {
            ports: make_headless_service(zk).spec.get_Some_0().ports,
            selector: make_headless_service(zk).spec.get_Some_0().selector,
            publish_not_ready_addresses: make_headless_service(zk).spec.get_Some_0().publish_not_ready_addresses,
            ..found_headless_service.spec.get_Some_0()
        }),
        ..found_headless_service
    }
}

pub open spec fn make_headless_service(zk: ZookeeperClusterView) -> ServiceView {
    let ports = seq![
        ServicePortView::default().set_name(new_strlit("tcp-client")@).set_port(zk.spec.ports.client),
        ServicePortView::default().set_name(new_strlit("tcp-quorum")@).set_port(zk.spec.ports.quorum),
        ServicePortView::default().set_name(new_strlit("tcp-leader-election")@).set_port(zk.spec.ports.leader_election),
        ServicePortView::default().set_name(new_strlit("tcp-metrics")@).set_port(zk.spec.ports.metrics),
        ServicePortView::default().set_name(new_strlit("tcp-admin-server")@).set_port(zk.spec.ports.admin_server)
    ];

    make_service(zk, make_headless_service_name(zk), ports, false)
}

}
