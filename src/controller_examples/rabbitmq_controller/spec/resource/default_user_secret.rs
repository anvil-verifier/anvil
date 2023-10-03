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
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::resource::rabbitmq_plugins::PluginsConfigMapBuilder;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct DefaultUserSecretBuilder {}

impl ResourceBuilder for DefaultUserSecretBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_default_user_secret_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, RabbitmqError> {
        Ok(make_default_user_secret(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, RabbitmqError> {
        let secret = SecretView::unmarshal(obj);
        if secret.is_Ok() {
            Ok(update_default_user_secret(rabbitmq, secret.get_Ok_0()).marshal())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn state_after_create_or_update(obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let sts = SecretView::unmarshal(obj);
        if sts.is_Ok() {
            Ok(state)
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn resource_state_matches(rabbitmq: RabbitmqClusterView, resources: StoredState) -> bool {
        let key = make_default_user_secret_key(rabbitmq);
        let obj = resources[key];
        &&& resources.contains_key(key)
        &&& SecretView::unmarshal(obj).is_Ok()
        &&& SecretView::unmarshal(obj).get_Ok_0().data == make_default_user_secret(rabbitmq).data
        &&& obj.metadata.labels == make_default_user_secret(rabbitmq).metadata.labels
        &&& obj.metadata.annotations == make_default_user_secret(rabbitmq).metadata.annotations
    }

    open spec fn unchangeable(object: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> bool {
        true
    }
}

pub open spec fn make_default_user_secret_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-default-user")@
}

pub open spec fn make_default_user_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: SecretView::kind(),
        name: make_default_user_secret_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_default_user_secret(rabbitmq: RabbitmqClusterView, found_secret: SecretView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_secret = make_default_user_secret(rabbitmq);
    SecretView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_secret.metadata.labels,
            annotations: made_secret.metadata.annotations,
            ..found_secret.metadata
        },
        data: Some(make_default_user_secret_data(rabbitmq)),
        ..found_secret
    }
}

pub open spec fn make_default_user_secret_data(rabbitmq: RabbitmqClusterView) -> Map<StringView, StringView>
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    Map::empty()
        .insert(new_strlit("username")@, new_strlit("user")@)
        .insert(new_strlit("password")@, new_strlit("changeme")@)
        .insert(new_strlit("type")@, new_strlit("rabbitmq")@)
        .insert(new_strlit("host")@,
            rabbitmq.metadata.name.get_Some_0() + new_strlit(".")@ + rabbitmq.metadata.namespace.get_Some_0() + new_strlit(".svc")@,
        )
        .insert(new_strlit("provider")@, new_strlit("rabbitmq")@)
        .insert(new_strlit("default_user.conf")@, new_strlit("default_user = user\ndefault_pass = changeme")@)
        .insert(new_strlit("port")@, new_strlit("5672")@)
}

pub open spec fn make_default_user_secret(rabbitmq: RabbitmqClusterView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    make_secret(rabbitmq, make_default_user_secret_name(rabbitmq), make_default_user_secret_data(rabbitmq))
}

}
