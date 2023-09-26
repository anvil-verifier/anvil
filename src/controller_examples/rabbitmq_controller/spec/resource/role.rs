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
use crate::rabbitmq_controller::spec::resource::role_binding::RoleBindingBuilder;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RoleBuilder {}

impl ResourceBuilder for RoleBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_role_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, RabbitmqError> {
        Ok(make_role(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, RabbitmqError> {
        let role = RoleView::unmarshal(obj);
        if role.is_Ok() {
            Ok(update_role(rabbitmq, role.get_Ok_0()).marshal())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn state_after_create_or_update(obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let role = RoleView::unmarshal(obj);
        if role.is_Ok() {
            Ok(RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, ResourceKind::RoleBinding),
                ..state
            })
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn resource_state_matches(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView) -> bool {
        &&& RoleView::unmarshal(obj).is_Ok()
        &&& RoleView::unmarshal(obj).get_Ok_0().policy_rules == make_role(rabbitmq).policy_rules
    }
}

pub open spec fn make_role_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-peer-discovery")@
}

pub open spec fn make_role_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: RoleView::kind(),
        name: make_role_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_role(rabbitmq: RabbitmqClusterView, found_role: RoleView) -> RoleView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_role = make_role(rabbitmq);
    RoleView {
        policy_rules: made_role.policy_rules,
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_role.metadata.labels,
            annotations: made_role.metadata.annotations,
            ..found_role.metadata
        },
        ..found_role
    }
}

pub open spec fn make_role(rabbitmq: RabbitmqClusterView) -> RoleView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    RoleView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_role_name(rabbitmq))
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        ).set_policy_rules(
            seq![
                PolicyRuleView::default().set_api_groups(seq![new_strlit("")@]).set_resources(seq![new_strlit("endpoints")@]).set_verbs(seq![new_strlit("get")@]),
                PolicyRuleView::default().set_api_groups(seq![new_strlit("")@]).set_resources(seq![new_strlit("events")@]).set_verbs(seq![new_strlit("create")@]),
            ]
        )
}

}
