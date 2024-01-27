// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::rabbitmq_controller::exec::resource::role_binding::RoleBindingBuilder;
use crate::rabbitmq_controller::model::resource as model_resource;
use crate::rabbitmq_controller::trusted::exec_types::*;
use crate::rabbitmq_controller::trusted::spec_types::RabbitmqClusterView;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct RoleBuilder {}

impl ResourceBuilder<RabbitmqCluster, RabbitmqReconcileState, model_resource::RoleBuilder> for RoleBuilder {
    open spec fn requirements(rabbitmq: RabbitmqClusterView) -> bool { rabbitmq.well_formed() }

    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Role::api_resource(),
            name: make_role_name(rabbitmq),
            namespace: rabbitmq.metadata().namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_role(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let role = Role::unmarshal(obj);
        if role.is_ok() {
            Ok(update_role(rabbitmq, role.unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn state_after_create(rabbitmq: &RabbitmqCluster, obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<KubeAPIRequest>), ()>) {
        let role = Role::unmarshal(obj);
        if role.is_ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::RoleBinding),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(RoleBindingBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    fn state_after_update(rabbitmq: &RabbitmqCluster, obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<KubeAPIRequest>), ()>) {
        let role = Role::unmarshal(obj);
        if role.is_ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::RoleBinding),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(RoleBindingBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub fn update_role(rabbitmq: &RabbitmqCluster, found_role: Role) -> (role: Role)
    requires rabbitmq@.well_formed(),
    ensures role@ == model_resource::update_role(rabbitmq@, found_role@),
{
    let mut role = found_role.clone();
    let made_role = make_role(rabbitmq);
    role.set_rules(make_rules(rabbitmq));
    role.set_metadata({
        let mut metadata = found_role.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_role.metadata().labels().unwrap());
        metadata.set_annotations(made_role.metadata().annotations().unwrap());
        metadata
    });
    role
}

pub fn make_role_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires rabbitmq@.well_formed(),
    ensures name@ == model_resource::make_role_name(rabbitmq@),
{
    rabbitmq.metadata().name().unwrap().concat(new_strlit("-peer-discovery"))
}

pub fn make_rules(rabbitmq: &RabbitmqCluster) -> (rules: Vec<PolicyRule>)
    requires rabbitmq@.well_formed(),
    ensures rules@.map_values(|r: PolicyRule| r@) == model_resource::make_role(rabbitmq@).policy_rules.get_Some_0(),
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
                    model_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[0].api_groups.get_Some_0()
                );
            }
            api_groups
        });
        rule.set_resources({
            let mut resources = Vec::new();
            resources.push(new_strlit("endpoints").to_string());
            proof{
                assert_seqs_equal!(
                    resources@.map_values(|p: String| p@),
                    model_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[0].resources.get_Some_0()
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
                    model_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[0].verbs
                );
            }
            verbs
        });
        rule
    });
    rules.push({
        let mut rule = PolicyRule::default();
        rule.set_api_groups({
            let mut api_groups = Vec::new();
            api_groups.push(new_strlit("").to_string());
            proof{
                assert_seqs_equal!(
                    api_groups@.map_values(|p: String| p@),
                    model_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[1].api_groups.get_Some_0()
                );
            }
            api_groups
        });
        rule.set_resources({
            let mut resources = Vec::new();
            resources.push(new_strlit("events").to_string());
            proof{
                assert_seqs_equal!(
                    resources@.map_values(|p: String| p@),
                    model_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[1].resources.get_Some_0()
                );
            }
            resources
        });
        rule.set_verbs({
            let mut verbs = Vec::new();
            verbs.push(new_strlit("create").to_string());
            proof{
                assert_seqs_equal!(
                    verbs@.map_values(|p: String| p@),
                    model_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[1].verbs
                );
            }
            verbs
        });
        rule
    });
    proof{
        assert_seqs_equal!(
            rules@.map_values(|p: PolicyRule| p@),
            model_resource::make_role(rabbitmq@).policy_rules.get_Some_0()
        );
    }
    rules
}

pub fn make_role(rabbitmq: &RabbitmqCluster) -> (role: Role)
    requires rabbitmq@.well_formed(),
    ensures role@ == model_resource::make_role(rabbitmq@),
{
    let mut role = Role::default();
    role.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_role_name(rabbitmq));
        metadata.set_namespace(rabbitmq.metadata().namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    role.set_rules(make_rules(rabbitmq));
    role
}

}
