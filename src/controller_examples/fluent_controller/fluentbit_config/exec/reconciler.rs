// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit_config::common::*;
use crate::fluent_controller::fluentbit_config::exec::types::*;
use crate::fluent_controller::fluentbit_config::spec::reconciler as fluent_spec;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, daemon_set::*, label_selector::*, object_meta::*,
    owner_reference::*, persistent_volume_claim::*, pod::*, pod_template_spec::*, resource::*,
    resource_requirements::*, role::*, role_binding::*, secret::*, service::*, service_account::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

// TODO:
// + Use Role after Anvil supports cluster-scoped resources
//
// + Add more features
//
// + Split the management logic into two reconciliation loops

pub struct FluentBitConfigReconcileState {
    pub reconcile_step: FluentBitConfigReconcileStep,
}

impl FluentBitConfigReconcileState {
    pub open spec fn to_view(&self) -> fluent_spec::FluentBitConfigReconcileState {
        fluent_spec::FluentBitConfigReconcileState {
            reconcile_step: self.reconcile_step,
        }
    }
}

pub struct FluentBitConfigReconciler {}

#[verifier(external)]
impl Reconciler<FluentBitConfig, FluentBitConfigReconcileState, EmptyType, EmptyType, EmptyAPIShimLayer> for FluentBitConfigReconciler {
    fn reconcile_init_state(&self) -> FluentBitConfigReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, fluentbit: &FluentBitConfig, resp_o: Option<Response<EmptyType>>, state: FluentBitConfigReconcileState) -> (FluentBitConfigReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(fluentbit, resp_o, state)
    }

    fn reconcile_done(&self, state: &FluentBitConfigReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(&self, state: &FluentBitConfigReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for FluentBitConfigReconciler {
    fn default() -> FluentBitConfigReconciler { FluentBitConfigReconciler{} }
}

pub fn reconcile_init_state() -> (state: FluentBitConfigReconcileState)
    ensures
        state.to_view() == fluent_spec::reconcile_init_state(),
{
    FluentBitConfigReconcileState {
        reconcile_step: FluentBitConfigReconcileStep::Init,
    }
}

pub fn reconcile_done(state: &FluentBitConfigReconcileState) -> (res: bool)
    ensures
        res == fluent_spec::reconcile_done(state.to_view()),
{
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &FluentBitConfigReconcileState) -> (res: bool)
    ensures
        res == fluent_spec::reconcile_error(state.to_view()),
{
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(fluentbit: &FluentBitConfig, resp_o: Option<Response<EmptyType>>, state: FluentBitConfigReconcileState) -> (res: (FluentBitConfigReconcileState, Option<Request<EmptyType>>))
    requires
        fluentbit@.metadata.name.is_Some(),
        fluentbit@.metadata.namespace.is_Some(),
    ensures
        (res.0.to_view(), opt_request_to_view(&res.1)) == fluent_spec::reconcile_core(fluentbit@, opt_response_to_view(&resp_o), state.to_view()),
{
    let step = state.reconcile_step;
    match step{
        FluentBitConfigReconcileStep::Init => {
            let secret = make_secret(fluentbit);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: Secret::api_resource(),
                namespace: fluentbit.metadata().namespace().unwrap(),
                obj: secret.marshal(),
            });
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::AfterCreateSecret,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        FluentBitConfigReconcileStep::AfterCreateSecret => {
            let req_o = None;
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::Done,
                ..state
            };
            (state_prime, req_o)
        },
        _ => {
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = None;
            (state_prime, req_o)
        }
    }
}


pub fn make_secret(fluentbit: &FluentBitConfig) -> (secret: Secret)
    requires
        fluentbit@.metadata.name.is_Some(),
        fluentbit@.metadata.namespace.is_Some(),
    ensures
        secret@ == fluent_spec::make_secret(fluentbit@),
{
    let mut secret = Secret::default();
    secret.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(fluentbit.metadata().name().unwrap());
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(fluentbit.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    fluent_spec::make_secret(fluentbit@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    secret.set_data({
        let mut data = StringMap::empty();
        data.insert(new_strlit("fluent-bit.conf").to_string(), fluentbit.spec().fluentbit_config());
        data.insert(new_strlit("parsers.conf").to_string(), fluentbit.spec().parsers_config());
        data
    });
    secret
}

}
