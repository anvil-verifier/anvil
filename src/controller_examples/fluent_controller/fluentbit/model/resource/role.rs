// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::model::resource::{
    common::*, role_binding::RoleBindingBuilder,
};
use crate::fluent_controller::fluentbit::trusted::{spec_types::*, step::*};
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RoleBuilder {}

impl ResourceBuilder<FluentBitView, FluentBitReconcileState> for RoleBuilder {
    open spec fn get_request(fb: FluentBitView) -> GetRequest {
        GetRequest { key: make_role_key(fb) }
    }

    open spec fn make(fb: FluentBitView, state: FluentBitReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_role(fb).marshal())
    }

    open spec fn update(fb: FluentBitView, state: FluentBitReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let role = RoleView::unmarshal(obj);
        if role.is_Ok() {
            Ok(update_role(fb, role.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
        let role = RoleView::unmarshal(obj);
        if role.is_Ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::RoleBinding),
                ..state
            };
            let req = APIRequest::GetRequest(RoleBindingBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
        let role = RoleView::unmarshal(obj);
        if role.is_Ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::RoleBinding),
                ..state
            };
            let req = APIRequest::GetRequest(RoleBindingBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_role_name(fb: FluentBitView) -> StringView { fb.metadata.name.get_Some_0() + new_strlit("-role")@ }

pub open spec fn make_role_key(fb: FluentBitView) -> ObjectRef {
    ObjectRef {
        kind: RoleView::kind(),
        name: make_role_name(fb),
        namespace: fb.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_role(fb: FluentBitView, found_role: RoleView) -> RoleView {
    let made_role = make_role(fb);
    RoleView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(fb)),
            finalizers: None,
            labels: made_role.metadata.labels,
            annotations: made_role.metadata.annotations,
            ..found_role.metadata
        },
        policy_rules: made_role.policy_rules,
        ..found_role
    }
}

pub open spec fn make_role(fb: FluentBitView) -> RoleView {
    RoleView {
        metadata: ObjectMetaView {
            name: Some(make_role_name(fb)),
            owner_references: Some(make_owner_references(fb)),
            labels: Some(make_labels(fb)),
            annotations: Some(fb.spec.annotations),
            ..ObjectMetaView::default()
        },
        policy_rules: Some(seq![
            PolicyRuleView {
                api_groups: Some(seq![new_strlit("")@]),
                resources: Some(seq![new_strlit("pods")@]),
                verbs: seq![new_strlit("get")@],
            }
        ]),
        ..RoleView::default()
    }
}

}
