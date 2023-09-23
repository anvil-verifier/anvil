// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::resource::erlang_cookie::ErlangCookieBuilder;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ServiceBuilder {}

impl ResourceBuilder<ServiceView> for ServiceBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_main_service_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, RabbitmqError> {
        Ok(make_main_service(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, RabbitmqError> {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            Ok(update_main_service(rabbitmq, service.get_Ok_0()).marshal())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn state_after_create_or_update(obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            Ok(RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, ResourceKind::ErlangCookieSecret),
                ..state
            })
        } else {
            Err(RabbitmqError::Error)
        }
    }
}

pub open spec fn make_main_service_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0()
}

pub open spec fn make_main_service_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_main_service_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_main_service(rabbitmq: RabbitmqClusterView, found_main_service: ServiceView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_main_service = make_main_service(rabbitmq);
    ServiceView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_main_service.metadata.labels,
            annotations: made_main_service.metadata.annotations,
            ..found_main_service.metadata
        },
        ..found_main_service
    }
}

pub open spec fn make_main_service(rabbitmq: RabbitmqClusterView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let ports = seq![
        ServicePortView::default().set_name(new_strlit("amqp")@).set_port(5672).set_app_protocol(new_strlit("amqp")@),
        ServicePortView::default().set_name(new_strlit("management")@).set_port(15672).set_app_protocol(new_strlit("http")@),
        ServicePortView::default().set_name(new_strlit("prometheus")@).set_port(15692).set_app_protocol(new_strlit("prometheus.io/metrics")@),
    ];
    make_service(rabbitmq, make_main_service_name(rabbitmq), ports, true)
}

}
