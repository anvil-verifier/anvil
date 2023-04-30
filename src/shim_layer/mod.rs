// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, custom_resource::*, error::*, object::*,
};
use crate::reconciler::exec::*;
use anyhow::Result;
use builtin::*;
use builtin_macros::*;
use deps_hack::{Error, SimpleCR};
use futures::TryFuture;
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

// TODO: revisit kube error
#[verifier(external)]
pub fn kube_error_to_ghost(error: &kube::Error) -> APIError {
    match error {
        kube::Error::Api(error_resp) => {
            if error_resp.code == 404 {
                APIError::ObjectNotFound
            } else if error_resp.code == 403 {
                APIError::ObjectAlreadyExists
            } else {
                APIError::Other
            }
        },
        _ => APIError::Other,
    }
}


#[verifier(external)]
pub fn error_policy(_object: Arc<SimpleCR>, _error: &Error, _ctx: Arc<Data>) -> Action {
    Action::requeue(Duration::from_secs(1))
}

// TODO: reconcile_with should not be hardcoded to SimpleCR
#[verifier(external)]
pub async fn reconcile_with<T, S>(reconciler: &T, cr: Arc<SimpleCR>, ctx: Arc<Data>) -> Result<Action, Error>
  where
    T: Reconciler<S>
{
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
    let mut state = reconciler.reconcile_init_state();
    let mut resp_option: Option<KubeAPIResponse> = Option::None;

    // Call reconcile_core in a loop
    loop {
        // If reconcile core is done, then breaks the loop
        if reconciler.reconcile_done(&state) {
            break;
        }
        // TODO: we should treat reconcile_error differently
        if reconciler.reconcile_error(&state) {
            break;
        }
        // Feed the current reconcile state and get the new state and the pending request
        let (state_prime, req_option) = reconciler.reconcile_core(&cr_key, &resp_option, &state);
        // Pattern match the request and send requests to the Kubernetes API via kube-rs methods
        match req_option {
            Option::Some(req) => match req {
                KubeAPIRequest::CustomResourceRequest(req) => {
                    match req {
                        KubeCustomResourceRequest::GetRequest(get_req) => {
                            let cr_api = Api::<SimpleCR>::namespaced(client.clone(), &get_req.namespace.into_rust_string());
                            match cr_api.get(&get_req.name.into_rust_string()).await {
                                std::result::Result::Err(err) => {
                                    resp_option = Option::Some(KubeAPIResponse::GetResponse(
                                        KubeGetResponse{
                                            res: vstd::result::Result::Err(kube_error_to_ghost(&err)),
                                        }
                                    ));
                                    println!("Get CR failed {}", err);
                                },
                                std::result::Result::Ok(obj) => {
                                    resp_option = Option::Some(KubeAPIResponse::GetResponse(
                                        KubeGetResponse{
                                            // TODO: need to use the actual returned object here
                                            res: vstd::result::Result::Ok(KubeObject::CustomResource(CustomResource::default())),
                                        }
                                    ));
                                    println!("Get CR done");
                                },
                            }
                        },
                        _ => {
                            resp_option = Option::None;
                        }
                    }
                },
                KubeAPIRequest::ConfigMapRequest(req) => {
                    match req {
                        KubeConfigMapRequest::CreateRequest(create_req) => {
                            let cm_api = Api::<k8s_openapi::api::core::v1::ConfigMap>::namespaced(client.clone(), &create_req.obj.kube_metadata_ref().namespace.as_ref().unwrap());
                            let pp = PostParams::default();
                            let cm = create_req.obj.into_kube_obj();
                            // TODO: need to prove whether the object is valid
                            // See an example:
                            // ConfigMap "foo_cm" is invalid: metadata.name: Invalid value: "foo_cm": a lowercase RFC 1123 subdomain must consist of lower case alphanumeric characters, '-' or '.',
                            // and must start and end with an alphanumeric character (e.g. 'example.com', regex used for validation is '[a-z0-9]([-a-z0-9]*[a-z0-9])?(\.[a-z0-9]([-a-z0-9]*[a-z0-9])?)*')
                            match cm_api.create(&pp, &cm).await {
                                std::result::Result::Err(err) => {
                                    resp_option = Option::Some(KubeAPIResponse::CreateResponse(
                                        KubeCreateResponse{
                                            res: vstd::result::Result::Err(kube_error_to_ghost(&err)),
                                        }
                                    ));
                                    println!("Create CM failed {}", err);
                                },
                                std::result::Result::Ok(obj) => {
                                    resp_option = Option::Some(KubeAPIResponse::GetResponse(
                                        KubeGetResponse{
                                            res: vstd::result::Result::Ok(KubeObject::ConfigMap(ConfigMap::from_kube_obj(obj))),
                                        }
                                    ));
                                    println!("Create CM done");
                                },
                            }
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
