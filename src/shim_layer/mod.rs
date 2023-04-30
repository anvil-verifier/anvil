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
use core::fmt::Debug;
use core::hash::Hash;
use deps_hack::{Error, SimpleCR};
use futures::StreamExt;
use futures::TryFuture;
use kube::{
    api::{Api, ListParams, ObjectMeta, PostParams, Resource},
    runtime::controller::{Action, Controller},
    Client, CustomResource, CustomResourceExt,
};
use serde::de::DeserializeOwned;
use std::sync::Arc;
use std::time::Duration;
use vstd::{option::*, string::*};

verus! {

/// The shim layer connects the verified reconciler to the trusted kube-rs APIs.
/// The key is to implement the reconcile function (impl FnMut(Arc<K>, Arc<Ctx>) -> ReconcilerFut),
/// which is required by the kube-rs framework to build a controller,
/// on top of reconcile_core, which is provided by the developer.

/// run_controller prepares and runs the controller. It requires:
/// K: the custom resource type
/// T: the reconciler type
/// S: the local state of the reconciler
#[verifier(external)]
pub async fn run_controller<K, T, S>() -> Result<()>
where
    K: Clone + Resource + CustomResourceExt + DeserializeOwned + Debug + Send + Sync + 'static,
    K::DynamicType: Default + Eq + Hash + Clone + Debug + Unpin,
    T: Reconciler<S> + Send + Sync + Default,
    S: Send
{
    let client = Client::try_default().await?;
    let crs = Api::<K>::all(client.clone());
    println!(
        "CRD:\n{}\n",
        serde_yaml::to_string(&K::crd())?
    );

    // Build the async closure on top of reconcile_with
    let reconcile = |cr: Arc<K>, ctx: Arc<Data>| async move {
        return reconcile_with::<K, T, S>(&T::default(), cr, ctx).await;
    };

    println!("starting controller");
    // TODO: the controller should also listen to the owned resources
    Controller::new(crs, ListParams::default()) // The controller's reconcile is triggered when a CR is created/updated
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { client })) // The reconcile function is registered
        .for_each(|res| async move {
            match res {
                Ok(o) => println!("reconciled {:?}", o),
                Err(e) => println!("reconcile failed: {}", e),
            }
        })
        .await;
    println!("controller terminated");
    Ok(())
}

/// reconcile_with implements the reconcile function by repeatedly invoking reconciler.reconcile_core.
/// reconcile_with will be invoked by kube-rs whenever kube-rs's watcher receives any event defined as relevant to the controller.
/// In each invocation, reconcile_with invokes reconciler.reconcile_core in a loop:
/// it starts with reconciler.reconcile_init_state, and in each iteration it invokes reconciler.reconcile_core with the new state
/// returned by the previous invocation.
/// For each request from reconciler.reconcile_core, it invokes kube-rs APIs to send the request to the Kubernetes API.
/// It ends the loop when the reconciler reports the reconcile is done (reconciler.reconcile_done) or encounters error (reconciler.reconcile_error).

#[verifier(external)]
pub async fn reconcile_with<K, T, S>(reconciler: &T, cr: Arc<K>, ctx: Arc<Data>) -> Result<Action, Error>
where
    K: Resource,
    T: Reconciler<S>,
{
    let client = &ctx.client;

    let cr_name = cr
        .meta()
        .name
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.name"))?;
    let cr_ns = cr
        .meta()
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
            println!("reconcile done");
            break;
        }
        if reconciler.reconcile_error(&state) {
            println!("reconcile error");
            return Err(Error::APIError);
        }
        // Feed the current reconcile state and get the new state and the pending request
        let (state_prime, req_option) = reconciler.reconcile_core(&cr_key, &resp_option, &state);
        // Pattern match the request and send requests to the Kubernetes API via kube-rs methods
        // TODO: use dynamic object type to avoid pattern matching each concrete type
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

    Ok(Action::requeue(Duration::from_secs(10)))
}

/// error_policy defines the controller's behavior when the reconcile ends with an error.

#[verifier(external)]
pub fn error_policy<K>(_object: Arc<K>, _error: &Error, _ctx: Arc<Data>) -> Action
where
    K: Clone + Resource + DeserializeOwned + Debug + Send + Sync + 'static,
    K::DynamicType: Eq + Hash + Clone + Debug + Unpin,
{
    Action::requeue(Duration::from_secs(10))
}

/// Data is passed to reconcile_with.
/// It carries the client that communicates with Kubernetes API.
#[verifier(external_body)]
pub struct Data {
    pub client: Client,
}

/// kube_error_to_ghost translates the API error from kube-rs APIs
/// to the form that can be processed by reconcile_core.

// TODO: revisit the translation; the current implementation is too coarse grained.
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

}
