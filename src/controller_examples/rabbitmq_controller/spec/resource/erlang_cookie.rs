// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ErlangCookieBuilder {}

impl ResourceBuilder<SecretView> for ErlangCookieBuilder {
    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<SecretView, RabbitmqError> {
        Ok(make_erlang_secret(rabbitmq))
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, found_resource: SecretView) -> Result<SecretView, RabbitmqError> {
        Ok(update_erlang_secret(rabbitmq, found_resource))
    }
}

pub open spec fn make_erlang_secret_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-erlang-cookie")@
}

pub open spec fn make_erlang_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: SecretView::kind(),
        name: make_erlang_secret_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_erlang_secret(rabbitmq: RabbitmqClusterView, found_erlang_secret: SecretView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
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

pub open spec fn make_erlang_secret(rabbitmq: RabbitmqClusterView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let cookie = random_encoded_string(24);
    let data = Map::empty()
        .insert(new_strlit(".erlang.cookie")@, cookie);
    make_secret(rabbitmq, make_erlang_secret_name(rabbitmq), data)
}

pub closed spec fn random_encoded_string(length: usize) -> StringView;

}