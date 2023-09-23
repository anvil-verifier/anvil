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
use crate::rabbitmq_controller::spec::resource::StatefulSetBuilder;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RoleBindingBuilder {}

impl ResourceBuilder<RoleBindingView> for RoleBindingBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_role_binding_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, RabbitmqError> {
        Ok(make_role_binding(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, RabbitmqError> {
        let rb = RoleBindingView::unmarshal(obj);
        if rb.is_Ok() {
            Ok(update_role_binding(rabbitmq, rb.get_Ok_0()).marshal())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn state_after_create_or_update(obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let rb = RoleBindingView::unmarshal(obj);
        if rb.is_Ok() {
            Ok(RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, ResourceKind::StatefulSet),
                ..state
            })
        } else {
            Err(RabbitmqError::Error)
        }
    }
}

pub open spec fn make_role_binding_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@
}

pub open spec fn make_role_binding_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: RoleBindingView::kind(),
        name: make_role_binding_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_role_binding(rabbitmq: RabbitmqClusterView, found_role_binding: RoleBindingView) -> RoleBindingView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_role_binding = make_role_binding(rabbitmq);
    RoleBindingView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_role_binding.metadata.labels,
            annotations: made_role_binding.metadata.annotations,
            ..found_role_binding.metadata
        },
        role_ref: made_role_binding.role_ref,
        subjects: made_role_binding.subjects,
        ..found_role_binding
    }
}

pub open spec fn make_role_binding(rabbitmq: RabbitmqClusterView) -> RoleBindingView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    RoleBindingView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_role_binding_name(rabbitmq))
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        ).set_role_ref(RoleRefView::default()
            .set_api_group(new_strlit("rbac.authorization.k8s.io")@)
            .set_kind(new_strlit("Role")@)
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-peer-discovery")@)
        ).set_subjects(seq![SubjectView::default()
            .set_kind(new_strlit("ServiceAccount")@)
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
        ])
}

}
