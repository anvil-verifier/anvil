// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::resource::default_user_secret::DefaultUserSecretBuilder;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ErlangCookieBuilder {}

impl ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState> for ErlangCookieBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_erlang_secret_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_erlang_secret(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let secret = SecretView::unmarshal(obj);
        if secret.is_Ok() {
            Ok(update_erlang_secret(rabbitmq, secret.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let secret = SecretView::unmarshal(obj);
        if secret.is_Ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::DefaultUserSecret),
                ..state
            };
            let req = APIRequest::GetRequest(DefaultUserSecretBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let secret = SecretView::unmarshal(obj);
        if secret.is_Ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::DefaultUserSecret),
                ..state
            };
            let req = APIRequest::GetRequest(DefaultUserSecretBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_erlang_secret_name(rabbitmq: RabbitmqClusterView) -> StringView { rabbitmq.metadata.name.get_Some_0() + new_strlit("-erlang-cookie")@ }

pub open spec fn make_erlang_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef {
    ObjectRef {
        kind: SecretView::kind(),
        name: make_erlang_secret_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_erlang_secret(rabbitmq: RabbitmqClusterView, found_erlang_secret: SecretView) -> SecretView {
    let made_erlang_secret = make_erlang_secret(rabbitmq);
    SecretView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_erlang_secret.metadata.labels,
            annotations: made_erlang_secret.metadata.annotations,
            ..found_erlang_secret.metadata
        },
        ..found_erlang_secret
    }
}

pub open spec fn make_erlang_secret(rabbitmq: RabbitmqClusterView) -> SecretView {
    let cookie = random_encoded_string(24);
    let data = Map::empty()
        .insert(new_strlit(".erlang.cookie")@, cookie);
    make_secret(rabbitmq, make_erlang_secret_name(rabbitmq), data)
}

}
