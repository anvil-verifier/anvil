// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::resource::role_binding::RoleBindingBuilder;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct RoleBuilder {}

impl ResourceBuilder<Role, spec_resource::RoleBuilder> for RoleBuilder {
    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Role::api_resource(),
            name: make_role_name(rabbitmq),
            namespace: rabbitmq.namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, RabbitmqError> {
        Ok(make_role(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, RabbitmqError> {
        let role = Role::unmarshal(obj);
        if role.is_ok() {
            Ok(update_role(rabbitmq, role.unwrap()).marshal())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    fn state_after_create_or_update(obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let role = Role::unmarshal(obj);
        if role.is_ok() {
            Ok(RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, ResourceKind::RoleBinding),
                ..state
            })
        } else {
            Err(RabbitmqError::Error)
        }
    }
}

pub fn update_role(rabbitmq: &RabbitmqCluster, found_role: Role) -> (role: Role)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        role@ == spec_resource::update_role(rabbitmq@, found_role@),
{
    let mut role = found_role.clone();
    let made_role = make_role(rabbitmq);
    role.set_policy_rules(make_policy_rules(rabbitmq));
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
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        name@ == spec_resource::make_role_name(rabbitmq@),
{
    rabbitmq.name().unwrap().concat(new_strlit("-peer-discovery"))
}

pub fn make_policy_rules(rabbitmq: &RabbitmqCluster) -> (rules: Vec<PolicyRule>)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        rules@.map_values(|r: PolicyRule| r@) == spec_resource::make_role(rabbitmq@).policy_rules.get_Some_0(),
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
                    spec_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[0].api_groups.get_Some_0()
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
                    spec_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[0].resources.get_Some_0()
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
                    spec_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[0].verbs
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
                    spec_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[1].api_groups.get_Some_0()
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
                    spec_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[1].resources.get_Some_0()
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
                    spec_resource::make_role(rabbitmq@).policy_rules.get_Some_0()[1].verbs
                );
            }
            verbs
        });
        rule
    });
    proof{
        assert_seqs_equal!(
            rules@.map_values(|p: PolicyRule| p@),
            spec_resource::make_role(rabbitmq@).policy_rules.get_Some_0()
        );
    }
    rules
}

pub fn make_role(rabbitmq: &RabbitmqCluster) -> (role: Role)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        role@ == spec_resource::make_role(rabbitmq@),
{
    let mut role = Role::default();
    role.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_role_name(rabbitmq));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    role.set_policy_rules(make_policy_rules(rabbitmq));
    role
}

}
