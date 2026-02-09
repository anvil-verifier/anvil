// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::resource::StatefulSetBuilder;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RoleBindingBuilder {}

impl ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState> for RoleBindingBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_role_binding_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_role_binding(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let rb = RoleBindingView::unmarshal(obj);
        if rb is Ok {
            Ok(update_role_binding(rabbitmq, rb->Ok_0).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let rb = RoleBindingView::unmarshal(obj);
        if rb is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::StatefulSet),
                ..state
            };
            let req = APIRequest::GetRequest(StatefulSetBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let rb = RoleBindingView::unmarshal(obj);
        if rb is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::StatefulSet),
                ..state
            };
            let req = APIRequest::GetRequest(StatefulSetBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_role_binding_name(rabbitmq: RabbitmqClusterView) -> StringView { RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + rabbitmq.metadata.name->0 + "-server"@ }

pub open spec fn make_role_binding_key(rabbitmq: RabbitmqClusterView) -> ObjectRef {
    ObjectRef {
        kind: RoleBindingView::kind(),
        name: make_role_binding_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace->0,
    }
}

pub open spec fn update_role_binding(rabbitmq: RabbitmqClusterView, found_role_binding: RoleBindingView) -> RoleBindingView {
    let made_role_binding = make_role_binding(rabbitmq);
    RoleBindingView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_role_binding.metadata.labels,
            annotations: made_role_binding.metadata.annotations,
            ..found_role_binding.metadata
        },
        subjects: made_role_binding.subjects,
        ..found_role_binding
    }
}

pub open spec fn make_role_binding(rabbitmq: RabbitmqClusterView) -> RoleBindingView {
    RoleBindingView::default()
        .with_metadata(ObjectMetaView::default()
            .with_name(make_role_binding_name(rabbitmq))
            .with_namespace(rabbitmq.metadata.namespace->0)
            .with_owner_references(make_owner_references(rabbitmq))
            .with_labels(make_labels(rabbitmq))
            .with_annotations(rabbitmq.spec.annotations)
        ).with_role_ref(RoleRefView::default()
            .with_api_group("rbac.authorization.k8s.io"@)
            .with_kind("Role"@)
            .with_name(rabbitmq.metadata.name->0 + "-peer-discovery"@)
        ).with_subjects(seq![SubjectView::default()
            .with_kind("ServiceAccount"@)
            .with_name(rabbitmq.metadata.name->0 + "-server"@)
            .with_namespace(rabbitmq.metadata.namespace->0)
        ])
}

}
