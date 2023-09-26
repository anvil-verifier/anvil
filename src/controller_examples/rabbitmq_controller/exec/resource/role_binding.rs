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
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::resource::stateful_set::StatefulSetBuilder;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct RoleBindingBuilder {}

impl ResourceBuilder<spec_resource::RoleBindingBuilder> for RoleBindingBuilder {
    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: RoleBinding::api_resource(),
            name: make_role_binding_name(rabbitmq),
            namespace: rabbitmq.namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, RabbitmqError> {
        Ok(make_role_binding(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, RabbitmqError> {
        let rb = RoleBinding::unmarshal(obj);
        if rb.is_ok() {
            Ok(update_role_binding(rabbitmq, rb.unwrap()).marshal())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    fn state_after_create_or_update(obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let rb = RoleBinding::unmarshal(obj);
        if rb.is_ok() {
            Ok(state)
        } else {
            Err(RabbitmqError::Error)
        }
    }
}

pub fn update_role_binding(rabbitmq: &RabbitmqCluster, found_role_binding: RoleBinding) -> (role_binding: RoleBinding)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        role_binding@ == spec_resource::update_role_binding(rabbitmq@, found_role_binding@),
{
    let mut role_binding = found_role_binding.clone();
    let made_role_binding = make_role_binding(rabbitmq);
    role_binding.set_role_ref(make_role_ref(rabbitmq));
    role_binding.set_subjects(make_subjects(rabbitmq));
    role_binding.set_metadata({
        let mut metadata = found_role_binding.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_role_binding.metadata().labels().unwrap());
        metadata.set_annotations(made_role_binding.metadata().annotations().unwrap());
        metadata
    });
    role_binding
}

pub fn make_role_binding_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        name@ == spec_resource::make_role_binding_name(rabbitmq@),
{
    rabbitmq.name().unwrap().concat(new_strlit("-server"))
}

pub fn make_role_ref(rabbitmq: &RabbitmqCluster) -> (role_ref: RoleRef)
    requires
        rabbitmq@.metadata.name.is_Some(),
    ensures
        role_ref@ == spec_resource::make_role_binding(rabbitmq@).role_ref
{
    let mut role_ref = RoleRef::default();
    role_ref.set_api_group(new_strlit("rbac.authorization.k8s.io").to_string());
    role_ref.set_kind(new_strlit("Role").to_string());
    role_ref.set_name(rabbitmq.name().unwrap().concat(new_strlit("-peer-discovery")));
    role_ref
}

pub fn make_subjects(rabbitmq: &RabbitmqCluster) -> (subjects: Vec<Subject>)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        subjects@.map_values(|s: Subject| s@) == spec_resource::make_role_binding(rabbitmq@).subjects.get_Some_0(),
{
    let mut subjects = Vec::new();
    subjects.push({
        let mut subject = Subject::default();
        subject.set_kind(new_strlit("ServiceAccount").to_string());
        subject.set_name(rabbitmq.name().unwrap().concat(new_strlit("-server")));
        subject.set_namespace(rabbitmq.namespace().unwrap());
        subject
    });
    proof{
        assert_seqs_equal!(
            subjects@.map_values(|p: Subject| p@),
            spec_resource::make_role_binding(rabbitmq@).subjects.get_Some_0()
        );
    }
    subjects
}

pub fn make_role_binding(rabbitmq: &RabbitmqCluster) -> (role_binding: RoleBinding)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        role_binding@ == spec_resource::make_role_binding(rabbitmq@),
{
    let mut role_binding = RoleBinding::default();
    role_binding.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_role_binding_name(rabbitmq));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    role_binding.set_role_ref(make_role_ref(rabbitmq));
    role_binding.set_subjects(make_subjects(rabbitmq));
    role_binding
}

}
