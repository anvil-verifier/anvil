// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::resource::rabbitmq_plugins::PluginsConfigMapBuilder;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct DefaultUserSecretBuilder {}

impl ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState> for DefaultUserSecretBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_default_user_secret_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_default_user_secret(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let secret = SecretView::unmarshal(obj);
        if secret is Ok {
            Ok(update_default_user_secret(rabbitmq, secret->Ok_0).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let sts = SecretView::unmarshal(obj);
        if sts is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::PluginsConfigMap),
                ..state
            };
            let req = APIRequest::GetRequest(PluginsConfigMapBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let secret = SecretView::unmarshal(obj);
        if secret is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::PluginsConfigMap),
                ..state
            };
            let req = APIRequest::GetRequest(PluginsConfigMapBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_default_user_secret_name(rabbitmq: RabbitmqClusterView) -> StringView { RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + rabbitmq.metadata.name->0 + "-default-user"@ }

pub open spec fn make_default_user_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef {
    ObjectRef {
        kind: SecretView::kind(),
        name: make_default_user_secret_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace->0,
    }
}

pub open spec fn update_default_user_secret(rabbitmq: RabbitmqClusterView, found_secret: SecretView) -> SecretView {
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

pub open spec fn make_default_user_secret_data(rabbitmq: RabbitmqClusterView) -> Map<StringView, StringView> {
    Map::empty()
        .insert("username"@, "user"@)
        .insert("password"@, "changeme"@)
        .insert("type"@, "rabbitmq"@)
        .insert("host"@,
            rabbitmq.metadata.name->0 + "."@ + rabbitmq.metadata.namespace->0 + ".svc"@,
        )
        .insert("provider"@, "rabbitmq"@)
        .insert("default_user.conf"@, "default_user = user\ndefault_pass = changeme"@)
        .insert("port"@, "5672"@)
}

pub open spec fn make_default_user_secret(rabbitmq: RabbitmqClusterView) -> SecretView {
    make_secret(rabbitmq, make_default_user_secret_name(rabbitmq), make_default_user_secret_data(rabbitmq))
}

}
