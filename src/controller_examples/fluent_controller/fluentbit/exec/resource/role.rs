// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::exec::resource::role_binding::RoleBindingBuilder;
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

pub struct RoleBuilder {}

impl ResourceBuilder<FluentBit, FluentBitReconcileState, model_resource::RoleBuilder> for RoleBuilder {
    open spec fn requirements(fb: FluentBitView) -> bool {
        fb.well_formed()
    }

    fn get_request(fb: &FluentBit) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Role::api_resource(),
            name: make_role_name(fb),
            namespace: fb.metadata().namespace().unwrap(),
        }
    }

    fn make(fb: &FluentBit, state: &FluentBitReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_role(fb).marshal())
    }

    fn update(fb: &FluentBit, state: &FluentBitReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let role = Role::unmarshal(obj);
        if role.is_ok() {
            Ok(update_role(fb, role.unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn state_after_create(fb: &FluentBit, obj: DynamicObject, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<KubeAPIRequest>), ()>) {
        let role = Role::unmarshal(obj);
        if role.is_ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::RoleBinding),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(RoleBindingBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    fn state_after_update(fb: &FluentBit, obj: DynamicObject, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<KubeAPIRequest>), ()>) {
        let role = Role::unmarshal(obj);
        if role.is_ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::RoleBinding),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(RoleBindingBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub fn update_role(fb: &FluentBit, found_role: Role) -> (role: Role)
    requires fb@.well_formed(),
    ensures role@ == model_resource::update_role(fb@, found_role@),
{
    let mut role = found_role.clone();
    let made_role = make_role(fb);
    role.set_rules(make_rules(fb));
    role.set_metadata({
        let mut metadata = found_role.metadata();
        metadata.set_owner_references(make_owner_references(fb));
        metadata.unset_finalizers();
        metadata.set_labels(made_role.metadata().labels().unwrap());
        metadata.set_annotations(made_role.metadata().annotations().unwrap());
        metadata
    });
    role
}

pub fn make_role_name(fb: &FluentBit) -> (name: String)
    requires fb@.well_formed(),
    ensures name@ == model_resource::make_role_name(fb@),
{
    fb.metadata().name().unwrap().concat(new_strlit("-role"))
}

pub fn make_rules(fb: &FluentBit) -> (rules: Vec<PolicyRule>)
    requires fb@.well_formed(),
    ensures rules@.map_values(|r: PolicyRule| r@) == model_resource::make_role(fb@).policy_rules.get_Some_0(),
{
    let mut rules = Vec::new();
    rules.push({
        let mut rule = PolicyRule::default();
        rule.set_api_groups({
            let mut api_groups = Vec::new();
            api_groups.push(new_strlit("").to_string());
            proof{
                assert_seqs_equal!(
                    api_groups@.map_values(|p: String| p@),
                    model_resource::make_role(fb@).policy_rules.get_Some_0()[0].api_groups.get_Some_0()
                );
            }
            api_groups
        });
        rule.set_resources({
            let mut resources = Vec::new();
            resources.push(new_strlit("pods").to_string());
            proof{
                assert_seqs_equal!(
                    resources@.map_values(|p: String| p@),
                    model_resource::make_role(fb@).policy_rules.get_Some_0()[0].resources.get_Some_0()
                );
            }
            resources
        });
        rule.set_verbs({
            let mut verbs = Vec::new();
            verbs.push(new_strlit("get").to_string());
            proof{
                assert_seqs_equal!(
                    verbs@.map_values(|p: String| p@),
                    model_resource::make_role(fb@).policy_rules.get_Some_0()[0].verbs
                );
            }
            verbs
        });
        rule
    });
    proof{
        assert_seqs_equal!(
            rules@.map_values(|p: PolicyRule| p@),
            model_resource::make_role(fb@).policy_rules.get_Some_0()
        );
    }
    rules
}

pub fn make_role(fb: &FluentBit) -> (role: Role)
    requires fb@.well_formed(),
    ensures role@ == model_resource::make_role(fb@),
{
    let mut role = Role::default();
    role.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_role_name(fb));
        metadata.set_owner_references(make_owner_references(fb));
        metadata.set_labels(make_labels(fb));
        metadata.set_annotations(fb.spec().annotations());
        metadata
    });
    role.set_rules(make_rules(fb));
    role
}

}
