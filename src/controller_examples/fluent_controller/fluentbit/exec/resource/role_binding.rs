// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::exec::resource::role::make_role_name;
use crate::fluent_controller::fluentbit::exec::resource::service::ServiceBuilder;
use crate::fluent_controller::fluentbit::exec::resource::service_account::make_service_account_name;
use crate::fluent_controller::fluentbit::model::resource as model_resource;
use crate::fluent_controller::fluentbit::trusted::{
    exec_types::*, spec_types::FluentBitView, step::*,
};
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct RoleBindingBuilder {}

impl ResourceBuilder<FluentBit, FluentBitReconcileState, model_resource::RoleBindingBuilder> for RoleBindingBuilder {
    open spec fn requirements(fb: FluentBitView) -> bool {
        fb.well_formed()
    }

    fn get_request(fb: &FluentBit) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: RoleBinding::api_resource(),
            name: make_role_binding_name(fb),
            namespace: fb.metadata().namespace().unwrap(),
        }
    }

    fn make(fb: &FluentBit, state: &FluentBitReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_role_binding(fb).marshal())
    }

    fn update(fb: &FluentBit, state: &FluentBitReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let rb = RoleBinding::unmarshal(obj);
        if rb.is_ok() {
            Ok(update_role_binding(fb, rb.unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn state_after_create(fb: &FluentBit, obj: DynamicObject, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<KubeAPIRequest>), ()>) {
        let rb = RoleBinding::unmarshal(obj);
        if rb.is_ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Service),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(ServiceBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    fn state_after_update(fb: &FluentBit, obj: DynamicObject, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<KubeAPIRequest>), ()>) {
        let rb = RoleBinding::unmarshal(obj);
        if rb.is_ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::Service),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(ServiceBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub fn update_role_binding(fb: &FluentBit, found_role_binding: RoleBinding) -> (role_binding: RoleBinding)
    requires fb@.well_formed(),
    ensures role_binding@ == model_resource::update_role_binding(fb@, found_role_binding@),
{
    let mut role_binding = found_role_binding.clone();
    let made_role_binding = make_role_binding(fb);
    role_binding.set_subjects(make_subjects(fb));
    role_binding.set_metadata({
        let mut metadata = found_role_binding.metadata();
        metadata.set_owner_references(make_owner_references(fb));
        metadata.unset_finalizers();
        metadata.set_labels(made_role_binding.metadata().labels().unwrap());
        metadata.set_annotations(made_role_binding.metadata().annotations().unwrap());
        metadata
    });
    role_binding
}

pub fn make_role_binding_name(fb: &FluentBit) -> (name: String)
    requires fb@.well_formed(),
    ensures name@ == model_resource::make_role_binding_name(fb@),
{
    fb.metadata().name().unwrap().concat(new_strlit("-role-binding"))
}

pub fn make_role_ref(fb: &FluentBit) -> (role_ref: RoleRef)
    requires fb@.well_formed(),
    ensures role_ref@ == model_resource::make_role_binding(fb@).role_ref
{
    let mut role_ref = RoleRef::default();
    role_ref.set_api_group(new_strlit("rbac.authorization.k8s.io").to_string());
    role_ref.set_kind(new_strlit("Role").to_string());
    role_ref.set_name(make_role_name(fb));
    role_ref
}

pub fn make_subjects(fb: &FluentBit) -> (subjects: Vec<Subject>)
    requires fb@.well_formed(),
    ensures subjects@.map_values(|s: Subject| s@) == model_resource::make_role_binding(fb@).subjects.get_Some_0(),
{
    let mut subjects = Vec::new();
    subjects.push({
        let mut subject = Subject::default();
        subject.set_kind(new_strlit("ServiceAccount").to_string());
        subject.set_name(make_service_account_name(fb));
        subject.set_namespace(fb.metadata().namespace().unwrap());
        subject
    });
    proof{
        assert_seqs_equal!(
            subjects@.map_values(|p: Subject| p@),
            model_resource::make_role_binding(fb@).subjects.get_Some_0()
        );
    }
    subjects
}

pub fn make_role_binding(fb: &FluentBit) -> (role_binding: RoleBinding)
    requires fb@.well_formed(),
    ensures role_binding@ == model_resource::make_role_binding(fb@),
{
    let mut role_binding = RoleBinding::default();
    role_binding.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_role_binding_name(fb));
        metadata.set_owner_references(make_owner_references(fb));
        metadata.set_labels(make_labels(fb));
        metadata.set_annotations(fb.spec().annotations());
        metadata
    });
    role_binding.set_role_ref(make_role_ref(fb));
    role_binding.set_subjects(make_subjects(fb));
    role_binding
}

}
