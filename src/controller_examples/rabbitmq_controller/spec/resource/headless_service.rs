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
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct HeadlessServiceBuilder {}

impl ResourceBuilder<ServiceView> for HeadlessServiceBuilder {
    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<ServiceView, RabbitmqError> {
        Ok(make_headless_service(rabbitmq))
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, found_resource: ServiceView) -> Result<ServiceView, RabbitmqError> {
        Ok(update_headless_service(rabbitmq, found_resource))
    }

    open spec fn get_result_check(obj: DynamicObjectView) -> Result<ServiceView, RabbitmqError> {
        let sts = ServiceView::unmarshal(obj);
        if sts.is_ok() {
            Ok(sts.get_Ok_0())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn create_result_check(obj: DynamicObjectView) -> Result<ServiceView, RabbitmqError> {
        let sts = ServiceView::unmarshal(obj);
        if sts.is_ok() {
            Ok(sts.get_Ok_0())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn update_result_check(obj: DynamicObjectView) -> Result<ServiceView, RabbitmqError> {
        let sts = ServiceView::unmarshal(obj);
        if sts.is_ok() {
            Ok(sts.get_Ok_0())
        } else {
            Err(RabbitmqError::Error)
        }
    }
}

pub open spec fn make_headless_service_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-nodes")@
}

pub open spec fn make_headless_service_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_headless_service_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_headless_service(rabbitmq: RabbitmqClusterView, found_headless_service: ServiceView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_service = make_headless_service(rabbitmq);
    ServiceView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_service.metadata.labels,
            annotations: made_service.metadata.annotations,
            ..found_headless_service.metadata
        },
        spec: made_service.spec,
        ..found_headless_service
    }
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
    make_service(rabbitmq, make_headless_service_name(rabbitmq), ports, false)
}

}
