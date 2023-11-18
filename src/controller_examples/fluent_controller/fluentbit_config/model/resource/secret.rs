// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::trusted::{spec_types::*, step::*};
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct SecretBuilder {}

impl ResourceBuilder<FluentBitConfigView, FluentBitConfigReconcileState> for SecretBuilder {
    open spec fn get_request(fbc: FluentBitConfigView) -> GetRequest {
        GetRequest { key: make_secret_key(fbc) }
    }

    open spec fn make(fbc: FluentBitConfigView, state: FluentBitConfigReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_secret(fbc).marshal())
    }

    open spec fn update(fbc: FluentBitConfigView, state: FluentBitConfigReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let secret = SecretView::unmarshal(obj);
        if secret.is_Ok() {
            Ok(update_secret(fbc, secret.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(fbc: FluentBitConfigView, obj: DynamicObjectView, state: FluentBitConfigReconcileState) -> (res: Result<(FluentBitConfigReconcileState, Option<APIRequest>), ()>) {
        let sts = SecretView::unmarshal(obj);
        if sts.is_Ok() {
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(fbc: FluentBitConfigView, obj: DynamicObjectView, state: FluentBitConfigReconcileState) -> (res: Result<(FluentBitConfigReconcileState, Option<APIRequest>), ()>) {
        let sts = SecretView::unmarshal(obj);
        if sts.is_Ok() {
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_secret_name(fbc: FluentBitConfigView) -> StringView {
    fbc.metadata.name.get_Some_0()
}

pub open spec fn make_secret_key(fbc: FluentBitConfigView) -> ObjectRef {
    ObjectRef {
        kind: SecretView::kind(),
        name: make_secret_name(fbc),
        namespace: fbc.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn make_secret(fbc: FluentBitConfigView) -> SecretView {
    SecretView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_secret_name(fbc))
            .set_owner_references(make_owner_references(fbc))
        ).set_data(Map::empty()
            .insert(new_strlit("fluent-bit.conf")@, fbc.spec.fluentbit_config)
            .insert(new_strlit("parsers.conf")@, fbc.spec.parsers_config)
        )
}

pub open spec fn update_secret(fbc: FluentBitConfigView, found_secret: SecretView) -> SecretView {
    let made_secret = make_secret(fbc);
    SecretView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(fbc)),
            finalizers: None,
            ..found_secret.metadata
        },
        data: Some(Map::empty()
            .insert(new_strlit("fluent-bit.conf")@, fbc.spec.fluentbit_config)
            .insert(new_strlit("parsers.conf")@, fbc.spec.parsers_config)
        ),
        ..found_secret
    }
}

}
