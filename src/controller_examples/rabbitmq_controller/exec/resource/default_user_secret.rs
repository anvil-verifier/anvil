// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::rabbitmq_controller::exec::resource::rabbitmq_plugins::PluginsConfigMapBuilder;
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

pub struct DefaultUserSecretBuilder {}

impl ResourceBuilder<RabbitmqCluster, RabbitmqReconcileState, model_resource::DefaultUserSecretBuilder> for DefaultUserSecretBuilder {
    open spec fn requirements(rabbitmq: RabbitmqClusterView) -> bool { rabbitmq.well_formed() }

    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Secret::api_resource(),
            name: make_default_user_secret_name(rabbitmq),
            namespace: rabbitmq.metadata().namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_default_user_secret(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let secret = Secret::unmarshal(obj);
        if secret.is_ok() {
            Ok(update_default_user_secret(rabbitmq, secret.unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn state_after_create(rabbitmq: &RabbitmqCluster, obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<KubeAPIRequest>), ()>) {
        let secret = Secret::unmarshal(obj);
        if secret.is_ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::PluginsConfigMap),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(PluginsConfigMapBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    fn state_after_update(rabbitmq: &RabbitmqCluster, obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<KubeAPIRequest>), ()>) {
        let secret = Secret::unmarshal(obj);
        if secret.is_ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::PluginsConfigMap),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(PluginsConfigMapBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub fn update_default_user_secret(rabbitmq: &RabbitmqCluster, found_secret: Secret) -> (secret: Secret)
    requires rabbitmq@.well_formed(),
    ensures secret@ == model_resource::update_default_user_secret(rabbitmq@, found_secret@),
{
    let mut user_secret = found_secret.clone();
    let made_user_secret = make_default_user_secret(rabbitmq);
    // TODO: whether to update ports
    user_secret.set_metadata({
        let mut metadata = found_secret.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_user_secret.metadata().labels().unwrap());
        metadata.set_annotations(made_user_secret.metadata().annotations().unwrap());
        metadata
    });
    user_secret.set_data(make_default_user_secret_data(rabbitmq));
    user_secret
}

pub fn make_default_user_secret_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires rabbitmq@.well_formed(),
    ensures name@ == model_resource::make_default_user_secret_name(rabbitmq@),
{
    rabbitmq.metadata().name().unwrap().concat(new_strlit("-default-user"))
}

pub fn make_default_user_secret_data(rabbitmq: &RabbitmqCluster) -> (data: StringMap)
    requires rabbitmq@.well_formed(),
    ensures data@ == model_resource::make_default_user_secret_data(rabbitmq@),
{
    let mut data = StringMap::empty();
    data.insert(new_strlit("username").to_string(), new_strlit("user").to_string());
    data.insert(new_strlit("password").to_string(), new_strlit("changeme").to_string());
    data.insert(new_strlit("type").to_string(), new_strlit("rabbitmq").to_string());
    data.insert(new_strlit("host").to_string(),
            rabbitmq.metadata().name().unwrap().concat(new_strlit(".")).concat(rabbitmq.metadata().namespace().unwrap().as_str()).concat(new_strlit(".svc"))
    );
    data.insert(new_strlit("provider").to_string(), new_strlit("rabbitmq").to_string());
    // TODO: check \n
    data.insert(new_strlit("default_user.conf").to_string(), new_strlit("default_user = user\ndefault_pass = changeme").to_string());
    data.insert(new_strlit("port").to_string(), new_strlit("5672").to_string());
    data
}

pub fn make_default_user_secret(rabbitmq: &RabbitmqCluster) -> (secret: Secret)
    requires rabbitmq@.well_formed(),
    ensures secret@ == model_resource::make_default_user_secret(rabbitmq@),
{
    make_secret(rabbitmq, make_default_user_secret_name(rabbitmq), make_default_user_secret_data(rabbitmq))
}

}
