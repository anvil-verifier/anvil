// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct AdminServerServiceBuilder {}

impl ResourceBuilder<ZookeeperClusterView, ZookeeperReconcileState> for AdminServerServiceBuilder {
    open spec fn get_request(rabbitmq: ZookeeperClusterView) -> GetRequest {
        GetRequest { key: make_admin_server_service_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: ZookeeperClusterView, state: ZookeeperReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_admin_server_service(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: ZookeeperClusterView, state: ZookeeperReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() && service.get_Ok_0().spec.is_Some() {
            Ok(update_admin_server_service(rabbitmq, service.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create_or_update(obj: DynamicObjectView, state: ZookeeperReconcileState) -> (res: Result<ZookeeperReconcileState, ()>) {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            Ok(state)
        } else {
            Err(())
        }
    }

    open spec fn resource_state_matches(rabbitmq: ZookeeperClusterView, resources: StoredState) -> bool {
        let key = make_admin_server_service_key(rabbitmq);
        let obj = resources[key];
        let made_spec = make_admin_server_service(rabbitmq).spec.get_Some_0();
        let spec = ServiceView::unmarshal(obj).get_Ok_0().spec.get_Some_0();
        &&& resources.contains_key(key)
        &&& ServiceView::unmarshal(obj).is_Ok()
        &&& ServiceView::unmarshal(obj).get_Ok_0().spec.is_Some()
        &&& made_spec == ServiceSpecView {
            cluster_ip: made_spec.cluster_ip,
            ..spec
        }
        &&& obj.metadata.labels == make_admin_server_service(rabbitmq).metadata.labels
        &&& obj.metadata.annotations == make_admin_server_service(rabbitmq).metadata.annotations
    }

    open spec fn unchangeable(object: DynamicObjectView, rabbitmq: ZookeeperClusterView) -> bool {
        true
    }
}

pub open spec fn make_admin_server_service_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_admin_server_service_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn make_admin_server_service_name(zk_name: StringView) -> StringView {
    zk_name + new_strlit("-admin-server")@
}

pub open spec fn update_admin_server_service(zk: ZookeeperClusterView, found_admin_server_service: ServiceView) -> ServiceView
    recommends
        zk.well_formed(),
{
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
            ..found_admin_server_service.spec.get_Some_0()
        }),
        ..found_admin_server_service
    }
}

pub open spec fn make_admin_server_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.well_formed(),
{
    let ports = seq![ServicePortView::default().set_name(new_strlit("tcp-admin-server")@).set_port(zk.spec.ports.admin_server)];

    make_service(zk, make_admin_server_service_name(zk.metadata.name.get_Some_0()), ports, true)
}

}