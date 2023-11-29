// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::model::resource::{
    common::*, role::make_role_name, service::ServiceBuilder,
    service_account::make_service_account_name,
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

pub struct RoleBindingBuilder {}

impl ResourceBuilder<FluentBitView, FluentBitReconcileState> for RoleBindingBuilder {
    open spec fn get_request(fb: FluentBitView) -> GetRequest {
        GetRequest { key: make_role_binding_key(fb) }
    }

    open spec fn make(fb: FluentBitView, state: FluentBitReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_role_binding(fb).marshal())
    }

    open spec fn update(fb: FluentBitView, state: FluentBitReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let rb = RoleBindingView::unmarshal(obj);
        if rb.is_Ok() {
            Ok(update_role_binding(fb, rb.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
        let rb = RoleBindingView::unmarshal(obj);
        if rb.is_Ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Service),
                ..state
            };
            let req = APIRequest::GetRequest(ServiceBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
        let rb = RoleBindingView::unmarshal(obj);
        if rb.is_Ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Service),
                ..state
            };
            let req = APIRequest::GetRequest(ServiceBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_role_binding_name(fb: FluentBitView) -> StringView { fb.metadata.name.get_Some_0() + new_strlit("-role-binding")@ }

pub open spec fn make_role_binding_key(fb: FluentBitView) -> ObjectRef {
    ObjectRef {
        kind: RoleBindingView::kind(),
        name: make_role_binding_name(fb),
        namespace: fb.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_role_binding(fb: FluentBitView, found_role_binding: RoleBindingView) -> RoleBindingView {
    let made_role_binding = make_role_binding(fb);
    RoleBindingView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(fb)),
            finalizers: None,
            labels: made_role_binding.metadata.labels,
            annotations: made_role_binding.metadata.annotations,
            ..found_role_binding.metadata
        },
        subjects: made_role_binding.subjects,
        ..found_role_binding
    }
}

pub open spec fn make_role_binding(fb: FluentBitView) -> RoleBindingView {
    RoleBindingView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_role_binding_name(fb))
            .set_owner_references(make_owner_references(fb))
            .set_labels(make_labels(fb))
            .set_annotations(fb.spec.annotations)
        ).set_role_ref(RoleRefView::default()
            .set_api_group(new_strlit("rbac.authorization.k8s.io")@)
            .set_kind(new_strlit("Role")@)
            .set_name(make_role_name(fb))
        ).set_subjects(seq![SubjectView::default()
            .set_kind(new_strlit("ServiceAccount")@)
            .set_name(make_service_account_name(fb))
            .set_namespace(fb.metadata.namespace.get_Some_0())
        ])
}

}
