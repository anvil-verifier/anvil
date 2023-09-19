// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::common::*;
use crate::fluent_controller::fluentbit_config::spec::types::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, daemon_set::*, dynamic::*, label_selector::*,
    object_meta::*, persistent_volume_claim::*, pod::*, pod_template_spec::*, resource::*, role::*,
    role_binding::*, secret::*, service::*, service_account::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct FluentBitConfigReconcileState {
    pub reconcile_step: FluentBitConfigReconcileStep,
}

pub struct FluentBitConfigReconciler {}

impl Reconciler<FluentBitConfigView, EmptyAPI> for FluentBitConfigReconciler {
    type T = FluentBitConfigReconcileState;

    open spec fn reconcile_init_state() -> FluentBitConfigReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        fluentbit_config: FluentBitConfigView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitConfigReconcileState
    ) -> (FluentBitConfigReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(fluentbit_config, resp_o, state)
    }

    open spec fn reconcile_done(state: FluentBitConfigReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: FluentBitConfigReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool {
        false // Don't expect anything from the user except the cr object
    }
}

pub open spec fn reconcile_init_state() -> FluentBitConfigReconcileState {
    FluentBitConfigReconcileState {
        reconcile_step: FluentBitConfigReconcileStep::Init,
    }
}

pub open spec fn reconcile_done(state: FluentBitConfigReconcileState) -> bool {
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: FluentBitConfigReconcileState) -> bool {
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(
    fluentbit_config: FluentBitConfigView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitConfigReconcileState
) -> (FluentBitConfigReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        fluentbit_config.metadata.name.is_Some(),
        fluentbit_config.metadata.namespace.is_Some(),
{
    let step = state.reconcile_step;
    match step{
        FluentBitConfigReconcileStep::Init => {
            let secret = make_secret(fluentbit_config);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: fluentbit_config.metadata.namespace.get_Some_0(),
                obj: secret.marshal(),
            });
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::AfterCreateSecret,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        FluentBitConfigReconcileStep::AfterCreateSecret => {
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::Done,
                ..state
            };
            (state_prime, None)
        },
        _ => {
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: step,
                ..state
            };
            (state_prime, None)
        }

    }
}

pub open spec fn reconcile_error_result(state: FluentBitConfigReconcileState) -> (FluentBitConfigReconcileState, Option<APIRequest>) {
    let state_prime = FluentBitConfigReconcileState {
        reconcile_step: FluentBitConfigReconcileStep::Error,
        ..state
    };
    let req_o = None;
    (state_prime, req_o)
}


pub open spec fn make_secret_name(fluentbit_config_name: StringView) -> StringView {
    fluentbit_config_name
}

pub open spec fn make_secret(fluentbit_config: FluentBitConfigView) -> SecretView
    recommends
        fluentbit_config.metadata.name.is_Some(),
        fluentbit_config.metadata.namespace.is_Some(),
{
    SecretView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_secret_name(fluentbit_config.metadata.name.get_Some_0()))
            .set_owner_references(seq![fluentbit_config.controller_owner_ref()])
        ).set_data(Map::empty()
            .insert(new_strlit("fluent-bit.conf")@, fluentbit_config.spec.fluentbit_config)
            .insert(new_strlit("parsers.conf")@, fluentbit_config.spec.parsers_config)
        )
}

}
