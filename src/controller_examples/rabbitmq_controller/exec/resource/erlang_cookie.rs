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
use crate::rabbitmq_controller::exec::resource::default_user_secret::DefaultUserSecretBuilder;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::rabbitmq_controller::spec::types::RabbitmqClusterView;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ErlangCookieBuilder {}

impl ResourceBuilder<RabbitmqCluster, RabbitmqReconcileState, spec_resource::ErlangCookieBuilder> for ErlangCookieBuilder {
    open spec fn requirements(rabbitmq: RabbitmqClusterView) -> bool {
        &&& rabbitmq.metadata.name.is_Some()
        &&& rabbitmq.metadata.namespace.is_Some()
    }

    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Secret::api_resource(),
            name: make_erlang_secret_name(rabbitmq),
            namespace: rabbitmq.metadata().namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_erlang_secret(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let secret = Secret::unmarshal(obj);
        if secret.is_ok() {
            Ok(update_erlang_secret(rabbitmq, secret.unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn state_after_create(rabbitmq: &RabbitmqCluster, obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<KubeAPIRequest>), ()>) {
        let secret = Secret::unmarshal(obj);
        if secret.is_ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::DefaultUserSecret),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(DefaultUserSecretBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    fn state_after_update(rabbitmq: &RabbitmqCluster, obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<KubeAPIRequest>), ()>) {
        let secret = Secret::unmarshal(obj);
        if secret.is_ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::DefaultUserSecret),
                ..state
            };
            let req = KubeAPIRequest::GetRequest(DefaultUserSecretBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub fn update_erlang_secret(rabbitmq: &RabbitmqCluster, found_erlang_secret: Secret) -> (secret: Secret)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        secret@ == spec_resource::update_erlang_secret(rabbitmq@, found_erlang_secret@),
{
    let mut erlang_secret = found_erlang_secret.clone();
    let made_secret = make_erlang_secret(rabbitmq);
    erlang_secret.set_metadata({
        let mut metadata = found_erlang_secret.metadata();
        let mut owner_references = Vec::new();
        owner_references.push(rabbitmq.controller_owner_ref());
        proof {
            assert_seqs_equal!(
                owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                spec_resource::update_erlang_secret(rabbitmq@, found_erlang_secret@).metadata.owner_references.get_Some_0()
            );
        }
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_secret.metadata().labels().unwrap());
        metadata.set_annotations(made_secret.metadata().annotations().unwrap());
        metadata
    });
    erlang_secret
}

pub fn make_erlang_secret_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        name@ == spec_resource::make_erlang_secret_name(rabbitmq@),
{
    rabbitmq.metadata().name().unwrap().concat(new_strlit("-erlang-cookie"))
}

pub fn make_erlang_secret(rabbitmq: &RabbitmqCluster) -> (secret: Secret)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        secret@ == spec_resource::make_erlang_secret(rabbitmq@)
{
    let mut data = StringMap::empty();
    let cookie = random_encoded_string(24);
    data.insert(new_strlit(".erlang.cookie").to_string(), cookie);
    make_secret(rabbitmq, make_erlang_secret_name(rabbitmq), data)
}

#[verifier(external_body)]
pub fn random_encoded_string(data_len: usize) -> (cookie: String)
    ensures
        cookie@ == spec_resource::random_encoded_string(data_len),
{
    let random_bytes: std::vec::Vec<std::primitive::u8> = (0..data_len).map(|_| deps_hack::rand::random::<std::primitive::u8>()).collect();
    String::from_rust_string(deps_hack::base64::encode(random_bytes))
}

}
