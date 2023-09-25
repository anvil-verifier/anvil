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
use crate::rabbitmq_controller::spec::resource::role::RoleBuilder;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ServiceAccountBuilder {}

impl ResourceBuilder<ServiceAccountView> for ServiceAccountBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_service_account_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, RabbitmqError> {
        Ok(make_service_account(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, RabbitmqError> {
        let sa = ServiceAccountView::unmarshal(obj);
        if sa.is_Ok() {
            Ok(update_service_account(rabbitmq, sa.get_Ok_0()).marshal())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn state_after_create_or_update(obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let sa = ServiceAccountView::unmarshal(obj);
        if sa.is_Ok() {
            Ok(RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, ResourceKind::Role),
                ..state
            })
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn resource_state_matches(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView) -> bool {
        true
    }
}

pub open spec fn make_service_account_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@
}

pub open spec fn make_service_account_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: ServiceAccountView::kind(),
        name: make_service_account_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_service_account(rabbitmq: RabbitmqClusterView, found_service_account: ServiceAccountView) -> ServiceAccountView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_service_account = make_service_account(rabbitmq);
    ServiceAccountView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_service_account.metadata.labels,
            annotations: made_service_account.metadata.annotations,
            ..found_service_account.metadata
        },
        ..found_service_account
    }
}

pub open spec fn make_service_account(rabbitmq: RabbitmqClusterView) -> ServiceAccountView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ServiceAccountView {
        metadata: ObjectMetaView {
            name: Some(make_service_account_name(rabbitmq)),
            namespace: rabbitmq.metadata.namespace,
            owner_references: Some(make_owner_references(rabbitmq)),
            labels: Some(make_labels(rabbitmq)),
            annotations: Some(rabbitmq.spec.annotations),
            ..ObjectMetaView::default()
        },
        ..ServiceAccountView::default()
    }
}

}
