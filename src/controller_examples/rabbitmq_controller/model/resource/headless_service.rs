// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::resource::service::ServiceBuilder;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct HeadlessServiceBuilder {}

impl ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState> for HeadlessServiceBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_headless_service_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_headless_service(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let service = ServiceView::unmarshal(obj);
        let found_service = service.get_Ok_0();
        if service.is_Ok() && found_service.spec.is_Some() {
            Ok(update_headless_service(rabbitmq, found_service).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Service),
                ..state
            };
            let req = APIRequest::GetRequest(ServiceBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Service),
                ..state
            };
            let req = APIRequest::GetRequest(ServiceBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_headless_service_name(rabbitmq: RabbitmqClusterView) -> StringView { rabbitmq.metadata.name.get_Some_0() + new_strlit("-nodes")@ }

pub open spec fn make_headless_service_key(rabbitmq: RabbitmqClusterView) -> ObjectRef {
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_headless_service_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_headless_service(rabbitmq: RabbitmqClusterView, found_headless_service: ServiceView) -> ServiceView {
    let made_headless_service = make_headless_service(rabbitmq);
    ServiceView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_headless_service.metadata.labels,
            annotations: made_headless_service.metadata.annotations,
            ..found_headless_service.metadata
        },
        spec: Some(ServiceSpecView {
            ports: made_headless_service.spec.get_Some_0().ports,
            selector: made_headless_service.spec.get_Some_0().selector,
            publish_not_ready_addresses: made_headless_service.spec.get_Some_0().publish_not_ready_addresses,
            ..found_headless_service.spec.get_Some_0()
        }),
        ..found_headless_service
    }
}

pub open spec fn make_headless_service(rabbitmq: RabbitmqClusterView) -> ServiceView {
    let mut ports = seq![
        ServicePortView::default().set_name(new_strlit("epmd")@).set_port(4369),
        ServicePortView::default().set_name(new_strlit("cluster-rpc")@).set_port(25672)
    ];
    make_service(rabbitmq, make_headless_service_name(rabbitmq), ports, false)
}

}
