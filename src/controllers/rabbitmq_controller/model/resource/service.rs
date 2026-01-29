// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::resource::erlang_cookie::ErlangCookieBuilder;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ServiceBuilder {}

impl ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState> for ServiceBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_main_service_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_main_service(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let service = ServiceView::unmarshal(obj);
        let found_service = service->Ok_0;
        if service is Ok && found_service.spec is Some {
            Ok(update_main_service(rabbitmq, found_service).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let service = ServiceView::unmarshal(obj);
        if service is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ErlangCookieSecret),
                ..state
            };
            let req = APIRequest::GetRequest(ErlangCookieBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let service = ServiceView::unmarshal(obj);
        if service is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ErlangCookieSecret),
                ..state
            };
            let req = APIRequest::GetRequest(ErlangCookieBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_main_service_name(rabbitmq: RabbitmqClusterView) -> StringView {
    rabbitmq.metadata.name->0 + "-client"@
}

pub open spec fn make_main_service_key(rabbitmq: RabbitmqClusterView) -> ObjectRef {
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_main_service_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace->0,
    }
}

pub open spec fn update_main_service(rabbitmq: RabbitmqClusterView, found_main_service: ServiceView) -> ServiceView {
    let made_main_service = make_main_service(rabbitmq);
    ServiceView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_main_service.metadata.labels,
            annotations: made_main_service.metadata.annotations,
            ..found_main_service.metadata
        },
        spec: Some(ServiceSpecView {
            ports: made_main_service.spec->0.ports,
            selector: made_main_service.spec->0.selector,
            publish_not_ready_addresses: made_main_service.spec->0.publish_not_ready_addresses,
            ..found_main_service.spec->0
        }),
        ..found_main_service
    }
}

pub open spec fn make_main_service(rabbitmq: RabbitmqClusterView) -> ServiceView {
    let ports = seq![
        ServicePortView::default().with_name("amqp"@).with_port(5672).with_app_protocol("amqp"@),
        ServicePortView::default().with_name("management"@).with_port(15672).with_app_protocol("http"@),
        ServicePortView::default().with_name("prometheus"@).with_port(15692).with_app_protocol("prometheus.io/metrics"@),
    ];
    make_service(rabbitmq, make_main_service_name(rabbitmq), ports, true)
}

}
