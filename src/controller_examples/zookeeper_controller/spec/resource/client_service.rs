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

pub struct ClientServiceBuilder {}

impl ResourceBuilder<ZookeeperClusterView, ZookeeperReconcileState> for ClientServiceBuilder {
    open spec fn get_request(zk: ZookeeperClusterView) -> GetRequest {
        GetRequest { key: make_client_service_key(zk) }
    }

    open spec fn make(zk: ZookeeperClusterView, state: ZookeeperReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_client_service(zk).marshal())
    }

    open spec fn update(zk: ZookeeperClusterView, state: ZookeeperReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() && service.get_Ok_0().spec.is_Some() {
            Ok(update_client_service(zk, service.get_Ok_0()).marshal())
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

    open spec fn resource_state_matches(zk: ZookeeperClusterView, resources: StoredState) -> bool {
        let key = make_client_service_key(zk);
        let obj = resources[key];
        let made_spec = make_client_service(zk).spec.get_Some_0();
        let spec = ServiceView::unmarshal(obj).get_Ok_0().spec.get_Some_0();
        &&& resources.contains_key(key)
        &&& ServiceView::unmarshal(obj).is_Ok()
        &&& ServiceView::unmarshal(obj).get_Ok_0().spec.is_Some()
        &&& made_spec == ServiceSpecView {
            cluster_ip: made_spec.cluster_ip,
            ..spec
        }
        &&& obj.metadata.labels == make_client_service(zk).metadata.labels
        &&& obj.metadata.annotations == make_client_service(zk).metadata.annotations
    }

    open spec fn unchangeable(object: DynamicObjectView, zk: ZookeeperClusterView) -> bool {
        true
    }
}

pub open spec fn make_client_service_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_client_service_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn make_client_service_name(zk_name: StringView) -> StringView {
    zk_name + new_strlit("-client")@
}

pub open spec fn update_client_service(zk: ZookeeperClusterView, found_client_service: ServiceView) -> ServiceView
    recommends
        zk.well_formed(),
{
    ServiceView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(zk)),
            finalizers: None,
            labels: make_client_service(zk).metadata.labels,
            annotations: make_client_service(zk).metadata.annotations,
            ..found_client_service.metadata
        },
        spec: Some(ServiceSpecView {
            ports: make_client_service(zk).spec.get_Some_0().ports,
            selector: make_client_service(zk).spec.get_Some_0().selector,
            ..found_client_service.spec.get_Some_0()
        }),
        ..found_client_service
    }
}

pub open spec fn make_client_service(zk: ZookeeperClusterView) -> ServiceView
    recommends
        zk.well_formed(),
{
    let ports = seq![ServicePortView::default().set_name(new_strlit("tcp-client")@).set_port(zk.spec.ports.client)];

    make_service(zk, make_client_service_name(zk.metadata.name.get_Some_0()), ports, true)
}

}