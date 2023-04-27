// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, config_map::*, object::*};
use crate::simple_controller::exec::reconciler::{
    reconcile_core, reconcile_done, reconcile_error, reconcile_init_state,
};
use anyhow::Result;
use builtin::*;
use builtin_macros::*;
use deps_hack::{Error, SimpleCR};
use k8s_openapi::api::core::v1::ConfigMap;
use kube::{
    api::{Api, ListParams, ObjectMeta, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResource, CustomResourceExt,
};
use std::sync::Arc;
use std::time::Duration;
use vstd::{option::*, string::*};

verus! {

#[verifier(external_body)]
pub struct Data {
    pub client: Client,
}

#[verifier(external)]
pub async fn reconcile(cr: Arc<SimpleCR>, ctx: Arc<Data>) -> Result<Action, Error> {
    let client = &ctx.client;

    let cr_name = cr
        .metadata
        .name
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.name"))?;
    let cr_ns = cr
        .metadata
        .namespace
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.namespace"))?;

    // Prepare the input for calling reconcile_core
    let cr_key = KubeObjectRef {
        kind: Kind::CustomResourceKind,
        name: String::from_rust_string(cr_name.clone()),
        namespace: String::from_rust_string(cr_ns.clone()),
    };
    let mut state = reconcile_init_state();
    let mut resp_option: Option<KubeAPIResponse> = Option::None;

    // Call reconcile_core in a loop
    loop {
        // If reconcile core is done, then breaks the loop
        if reconcile_done(&state) {
            break;
        }
        if reconcile_error(&state) {
            break;
        }
        // Feed the current reconcile state and get the new state and the pending request
        let (state_prime, req_option) = reconcile_core(&cr_key, &resp_option, &state);
        // Pattern match the request and send requests to the Kubernetes API via kube-rs methods
        match req_option {
            Option::Some(req) => match req {
                KubeAPIRequest::CustomResourceRequest(req) => {
                    match req {
                        KubeCustomResourceRequest::GetRequest(get_req) => {
                            let cr_api = Api::<SimpleCR>::namespaced(client.clone(), &get_req.namespace.into_rust_string());
                            cr_api.get(&get_req.name.into_rust_string()).await;
                            resp_option = Option::None;
                        },
                        _ => {
                            resp_option = Option::None;
                        }
                    }
                },
                KubeAPIRequest::ConfigMapRequest(req) => {
                    match req {
                        KubeConfigMapRequest::CreateRequest(create_req) => {
                            let cm_api = Api::<ConfigMap>::namespaced(client.clone(), &create_req.obj.metadata().namespace().unwrap().into_rust_string());
                            let pp = PostParams::default();
                            let cm = create_req.obj.into_kube_obj();
                            cm_api.create(&pp, &cm).await;
                            resp_option = Option::None;
                        },
                        _ => {
                            resp_option = Option::None;
                        }
                    }
                },
            },
            _ => resp_option = Option::None,
        }
        state = state_prime;
    }

    println!("reconcile OK");
    Ok(Action::requeue(Duration::from_secs(10)))
}

}
