// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, label_selector::*, object_meta::*,
    persistent_volume_claim::*, pod::*, pod_template_spec::*, resource::*, service::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::rabbitmqcluster::*;
use crate::reconciler::spec::*;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RabbitmqReconcileState {
    pub reconcile_step: RabbitmqReconcileStep,

    pub rabbitmq: Option<RabbitmqClusterView>,
}

pub open spec fn reconcile_init_state() -> RabbitmqReconcileState {
    RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Init,
        rabbitmq: Option::None,
    }
}

pub open spec fn reconcile_done(state: RabbitmqReconcileState) -> bool {
    match state.reconcile_step {
        RabbitmqReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: RabbitmqReconcileState) -> bool {
    match state.reconcile_step {
        RabbitmqReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(rabbitmq_ref: ObjectRef, resp_o: Option<APIResponse>, state: RabbitmqReconcileState) -> (RabbitmqReconcileState, Option<APIRequest>)
    recommends
        rabbitmq_ref.kind.is_CustomResourceKind(),
{
    let step = state.reconcile_step;
    match step{
        RabbitmqReconcileStep::Init => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterGetRabbitmq,
                ..state
            };
            let req_o =  Option::Some(APIRequest::GetRequest(GetRequest{key: rabbitmq_ref}));
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterGetRabbitmq => {
            let resp = resp_o.get_Some_0();
            let rabbitmq = RabbitmqClusterView::from_dynamic_object(resp.get_GetResponse_0().res.get_Ok_0());
            if !resp_o.is_Some()
                || !(resp.is_GetResponse() && resp.get_GetResponse_0().res.is_Ok())
                || !(rabbitmq.metadata.name.is_Some() && rabbitmq.metadata.namespace.is_Some()) {
                reconcile_error_result(state)
            } else {
                let headless_service = make_headless_service(rabbitmq);
                let req_o = Option::Some(APIRequest::CreateRequest(CreateRequest{
                    obj: headless_service.to_dynamic_object(),
                }));
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterCreateHeadlessService,
                    rabbitmq: Option::Some(rabbitmq),
                    ..state
                };
                (state_prime, req_o)
            }
        },
        _ => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = Option::None;
            (state_prime, req_o)
        }

    }
}


pub open spec fn reconcile_error_result(state: RabbitmqReconcileState) -> (RabbitmqReconcileState, Option<APIRequest>) {
    let state_prime = RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Error,
        ..state
    };
    let req_o = Option::None;
    (state_prime, req_o)
}


pub open spec fn make_headless_service(rabbitmq: RabbitmqClusterView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let mut ports = seq![
        ServicePortView::default().set_name(new_strlit("epmd")@).set_port(4369),
        ServicePortView::default().set_name(new_strlit("cluster-rpc")@).set_port(25672)
    ];

    make_service(rabbitmq, rabbitmq.metadata.name.get_Some_0() + new_strlit("-nodes")@, ports, false)
}

pub open spec fn make_main_service(rabbitmq: RabbitmqClusterView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let ports = seq![
        ServicePortView::default().set_name(new_strlit("amqp")@).set_port(5672).set_app_protocol(new_strlit("amqp")@),
        ServicePortView::default().set_name(new_strlit("management")@).set_port(15672).set_app_protocol(new_strlit("http")@),
    ];


    make_service(rabbitmq, rabbitmq.metadata.name.get_Some_0(), ports, false)
}

pub open spec fn make_service(
    rabbitmq: RabbitmqClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool
) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ServiceView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(name)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_labels(Map::empty().insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()))
        ).set_spec({
            let spec = ServiceSpecView::default()
                .set_ports(ports)
                .set_selector(Map::empty()
                    .insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0())
                ).set_publish_not_ready_addresses(true);
            if !cluster_ip {
                spec.set_cluster_ip(new_strlit("None")@)
            } else {
                spec
            }
        })
}


}
