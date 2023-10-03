// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit_config::common::*;
use crate::fluent_controller::fluentbit_config::exec::types::*;
use crate::fluent_controller::fluentbit_config::spec::reconciler as fbc_spec;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, daemon_set::*, label_selector::*, object_meta::*,
    owner_reference::*, persistent_volume_claim::*, pod::*, pod_template_spec::*, resource::*,
    resource_requirements::*, role::*, role_binding::*, secret::*, service::*, service_account::*,
};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct FluentBitConfigReconcileState {
    pub reconcile_step: FluentBitConfigReconcileStep,
}

impl FluentBitConfigReconcileState {
    pub open spec fn to_view(&self) -> fbc_spec::FluentBitConfigReconcileState {
        fbc_spec::FluentBitConfigReconcileState {
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

    fn reconcile_core(&self, fbc: &FluentBitConfig, resp_o: Option<Response<EmptyType>>, state: FluentBitConfigReconcileState) -> (FluentBitConfigReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(fbc, resp_o, state)
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
        state.to_view() == fbc_spec::reconcile_init_state(),
{
    FluentBitConfigReconcileState {
        reconcile_step: FluentBitConfigReconcileStep::Init,
    }
}

pub fn reconcile_done(state: &FluentBitConfigReconcileState) -> (res: bool)
    ensures
        res == fbc_spec::reconcile_done(state.to_view()),
{
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &FluentBitConfigReconcileState) -> (res: bool)
    ensures
        res == fbc_spec::reconcile_error(state.to_view()),
{
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(fbc: &FluentBitConfig, resp_o: Option<Response<EmptyType>>, state: FluentBitConfigReconcileState) -> (res: (FluentBitConfigReconcileState, Option<Request<EmptyType>>))
    requires
        fbc@.well_formed(),
    ensures
        (res.0.to_view(), opt_request_to_view(&res.1)) == fbc_spec::reconcile_core(fbc@, opt_response_to_view(&resp_o), state.to_view()),
{
    let step = state.reconcile_step;
    match step{
        FluentBitConfigReconcileStep::Init => {
            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: Secret::api_resource(),
                name: fbc.metadata().name().unwrap(),
                namespace: fbc.metadata().namespace().unwrap(),
            });
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::AfterGetSecret,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        FluentBitConfigReconcileStep::AfterGetSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_secret_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_secret_resp.is_ok() {
                    let unmarshal_secret_result = Secret::unmarshal(get_secret_resp.unwrap());
                    if unmarshal_secret_result.is_ok() {
                        let found_secret = unmarshal_secret_result.unwrap();
                        let new_secret = update_secret(fbc, &found_secret);
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: Secret::api_resource(),
                            name: make_secret_name(fbc),
                            namespace: fbc.metadata().namespace().unwrap(),
                            obj: new_secret.marshal(),
                        });
                        let state_prime = FluentBitConfigReconcileState {
                            reconcile_step: FluentBitConfigReconcileStep::AfterUpdateSecret,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_secret_resp.unwrap_err().is_object_not_found() {
                    let secret = make_secret(fbc);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Secret::api_resource(),
                        namespace: fbc.metadata().namespace().unwrap(),
                        obj: secret.marshal(),
                    });
                    let state_prime = FluentBitConfigReconcileState {
                        reconcile_step: FluentBitConfigReconcileStep::AfterCreateSecret,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitConfigReconcileStep::AfterCreateSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.unwrap().into_k_response().into_create_response().res.is_ok() {
                let state_prime = FluentBitConfigReconcileState {
                    reconcile_step: FluentBitConfigReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            }
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitConfigReconcileStep::AfterUpdateSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.unwrap().into_k_response().into_update_response().res.is_ok() {
                let state_prime = FluentBitConfigReconcileState {
                    reconcile_step: FluentBitConfigReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            }
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
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

pub fn make_owner_references(fbc: &FluentBitConfig) -> (owner_references: Vec<OwnerReference>)
    requires
        fbc@.well_formed(),
    ensures
        owner_references@.map_values(|or: OwnerReference| or@) == fbc_spec::make_owner_references(fbc@),
{
    let mut owner_references = Vec::new();
    owner_references.push(fbc.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
            fbc_spec::make_owner_references(fbc@)
        );
    }
    owner_references
}

fn make_secret_name(fbc: &FluentBitConfig) -> (name: String)
    requires
        fbc@.well_formed(),
    ensures
        name@ == fbc_spec::make_secret_name(fbc@.metadata.name.get_Some_0()),
{
    fbc.metadata().name().unwrap()
}

pub fn make_secret(fbc: &FluentBitConfig) -> (secret: Secret)
    requires
        fbc@.well_formed(),
    ensures
        secret@ == fbc_spec::make_secret(fbc@),
{
    let mut secret = Secret::default();
    secret.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_secret_name(fbc));
        metadata.set_owner_references(make_owner_references(fbc));
        metadata
    });
    secret.set_data({
        let mut data = StringMap::empty();
        data.insert(new_strlit("fluent-bit.conf").to_string(), fbc.spec().fluentbit_config());
        data.insert(new_strlit("parsers.conf").to_string(), fbc.spec().parsers_config());
        data
    });
    secret
}

fn update_secret(fbc: &FluentBitConfig, found_secret: &Secret) -> (secret: Secret)
    requires
        fbc@.well_formed(),
    ensures
        secret@ == fbc_spec::update_secret(fbc@, found_secret@),
{
    let mut secret = found_secret.clone();
    let made_secret = make_secret(fbc);
    secret.set_metadata({
        let mut metadata = found_secret.metadata();
        metadata.set_owner_references(make_owner_references(fbc));
        metadata.unset_finalizers();
        metadata
    });
    secret.set_data(made_secret.data().unwrap());
    secret
}

}
