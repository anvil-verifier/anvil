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

pub struct ServiceAccountBuilder {}

impl ResourceBuilder<ServiceAccountView> for ServiceAccountBuilder {
    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<ServiceAccountView, RabbitmqError> {
        Ok(make_service_account(rabbitmq))
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, found_resource: ServiceAccountView) -> Result<ServiceAccountView, RabbitmqError> {
        Ok(update_service_account(rabbitmq, found_resource))
    }

    open spec fn get_result_check(obj: DynamicObjectView) -> Result<ServiceAccountView, RabbitmqError> {
        let sts = ServiceAccountView::unmarshal(obj);
        if sts.is_ok() {
            Ok(sts.get_Ok_0())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn create_result_check(obj: DynamicObjectView) -> Result<ServiceAccountView, RabbitmqError> {
        let sts = ServiceAccountView::unmarshal(obj);
        if sts.is_ok() {
            Ok(sts.get_Ok_0())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn update_result_check(obj: DynamicObjectView) -> Result<ServiceAccountView, RabbitmqError> {
        let sts = ServiceAccountView::unmarshal(obj);
        if sts.is_ok() {
            Ok(sts.get_Ok_0())
        } else {
            Err(RabbitmqError::Error)
        }
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
