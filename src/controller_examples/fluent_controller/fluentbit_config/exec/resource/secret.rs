// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit_config::model::resource as model_resource;
use crate::fluent_controller::fluentbit_config::trusted::{
    exec_types::*, spec_types::FluentBitConfigView, step::*,
};
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct SecretBuilder {}

impl ResourceBuilder<FluentBitConfig, FluentBitConfigReconcileState, model_resource::SecretBuilder> for SecretBuilder {
    open spec fn requirements(fbc: FluentBitConfigView) -> bool { fbc.well_formed() }

    fn get_request(fbc: &FluentBitConfig) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: Secret::api_resource(),
            name: make_secret_name(fbc),
            namespace: fbc.metadata().namespace().unwrap(),
        }
    }

    fn make(fbc: &FluentBitConfig, state: &FluentBitConfigReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_secret(fbc).marshal())
    }

    fn update(fbc: &FluentBitConfig, state: &FluentBitConfigReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let secret = Secret::unmarshal(obj);
        if secret.is_ok() {
            Ok(update_secret(fbc, secret.unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn state_after_create(fbc: &FluentBitConfig, obj: DynamicObject, state: FluentBitConfigReconcileState) -> (res: Result<(FluentBitConfigReconcileState, Option<KubeAPIRequest>), ()>) {
        let secret = Secret::unmarshal(obj);
        if secret.is_ok() {
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }

    fn state_after_update(fbc: &FluentBitConfig, obj: DynamicObject, state: FluentBitConfigReconcileState) -> (res: Result<(FluentBitConfigReconcileState, Option<KubeAPIRequest>), ()>) {
        let secret = Secret::unmarshal(obj);
        if secret.is_ok() {
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

pub fn update_secret(fbc: &FluentBitConfig, found_secret: Secret) -> (secret: Secret)
    requires fbc@.well_formed(),
    ensures secret@ == model_resource::update_secret(fbc@, found_secret@),
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

pub fn make_secret_name(fbc: &FluentBitConfig) -> (name: String)
    requires fbc@.well_formed(),
    ensures name@ == model_resource::make_secret_name(fbc@),
{
    fbc.metadata().name().unwrap()
}

pub fn make_secret(fbc: &FluentBitConfig) -> (secret: Secret)
    requires fbc@.well_formed(),
    ensures secret@ == model_resource::make_secret(fbc@),
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

}
