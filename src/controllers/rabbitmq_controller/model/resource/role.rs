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
use crate::rabbitmq_controller::model::resource::role_binding::RoleBindingBuilder;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RoleBuilder {}

impl ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState> for RoleBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_role_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_role(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let role = RoleView::unmarshal(obj);
        if role is Ok {
            Ok(update_role(rabbitmq, role->Ok_0).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let role = RoleView::unmarshal(obj);
        if role is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::RoleBinding),
                ..state
            };
            let req = APIRequest::GetRequest(RoleBindingBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let role = RoleView::unmarshal(obj);
        if role is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::RoleBinding),
                ..state
            };
            let req = APIRequest::GetRequest(RoleBindingBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_role_name(rabbitmq: RabbitmqClusterView) -> StringView { rabbitmq.metadata.name->0 + "-peer-discovery"@ }

pub open spec fn make_role_key(rabbitmq: RabbitmqClusterView) -> ObjectRef {
    ObjectRef {
        kind: RoleView::kind(),
        name: make_role_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace->0,
    }
}

pub open spec fn update_role(rabbitmq: RabbitmqClusterView, found_role: RoleView) -> RoleView {
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

pub open spec fn make_role(rabbitmq: RabbitmqClusterView) -> RoleView {
    RoleView::default()
        .with_metadata(ObjectMetaView::default()
            .with_name(make_role_name(rabbitmq))
            .with_namespace(rabbitmq.metadata.namespace->0)
            .with_owner_references(make_owner_references(rabbitmq))
            .with_labels(make_labels(rabbitmq))
            .with_annotations(rabbitmq.spec.annotations)
        ).with_rules(
            seq![
                PolicyRuleView::default().with_api_groups(seq![""@]).with_resources(seq!["endpoints"@]).with_verbs(seq!["get"@]),
                PolicyRuleView::default().with_api_groups(seq![""@]).with_resources(seq!["events"@]).with_verbs(seq!["create"@]),
            ]
        )
}

}
