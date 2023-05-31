// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, dynamic::*, error::*, resource::*};
use crate::reconciler::exec::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use core::hash::Hash;
use deps_hack::anyhow::Result;
use deps_hack::futures::StreamExt;
use deps_hack::futures::TryFuture;
use deps_hack::kube::{
    api::{Api, ListParams, ObjectMeta, PostParams, Resource},
    runtime::controller::{Action, Controller},
    Client, CustomResource, CustomResourceExt,
};
use deps_hack::kube_core::{ErrorResponse, NamespaceResourceScope};
use deps_hack::serde::{de::DeserializeOwned, Serialize};
use deps_hack::Error;
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
/// ResourceWrapperType: the resource wrapper type
/// ReconcilerType: the reconciler type
/// ReconcileStateType: the local state of the reconciler
#[verifier(external)]
pub async fn run_controller<K, ResourceWrapperType, ReconcilerType, ReconcileStateType>() -> Result<()>
where
    K: Clone + Resource<Scope = NamespaceResourceScope> + CustomResourceExt + DeserializeOwned + Debug + Send + Serialize + Sync + 'static,
    K::DynamicType: Default + Eq + Hash + Clone + Debug + Unpin,
    ResourceWrapperType: ResourceWrapper<K> + Send,
    ReconcilerType: Reconciler<ResourceWrapperType, ReconcileStateType> + Send + Sync + Default,
    ReconcileStateType: Send
{
    let client = Client::try_default().await?;
    let crs = Api::<K>::all(client.clone());

    // Build the async closure on top of reconcile_with
    let reconcile = |cr: Arc<K>, ctx: Arc<Data>| async move {
        return reconcile_with::<K, ResourceWrapperType, ReconcilerType, ReconcileStateType>(
            &ReconcilerType::default(), cr, ctx
        ).await;
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
/// reconcile_with will be invoked by kube-rs whenever kube-rs's watcher receives any relevant event to the controller.
/// In each invocation, reconcile_with invokes reconciler.reconcile_core in a loop:
/// it starts with reconciler.reconcile_init_state, and in each iteration it invokes reconciler.reconcile_core
/// with the new state returned by the previous invocation.
/// For each request from reconciler.reconcile_core, it invokes kube-rs APIs to send the request to the Kubernetes API.
/// It ends the loop when the reconciler reports the reconcile is done (reconciler.reconcile_done)
/// or encounters error (reconciler.reconcile_error).

#[verifier(external)]
pub async fn reconcile_with<K, ResourceWrapperType, ReconcilerType, ReconcileStateType>(
    reconciler: &ReconcilerType, cr: Arc<K>, ctx: Arc<Data>
) -> Result<Action, Error>
where
    K: Clone + Resource<Scope = NamespaceResourceScope> + CustomResourceExt + DeserializeOwned + Debug + Serialize,
    K::DynamicType: Default + Clone + Debug,
    ResourceWrapperType: ResourceWrapper<K>,
    ReconcilerType: Reconciler<ResourceWrapperType, ReconcileStateType>,
{
    let client = &ctx.client;

    let cr_name = cr.meta().name.as_ref().ok_or_else(|| Error::MissingObjectKey(".metadata.name"))?;
    let cr_ns = cr.meta().namespace.as_ref().ok_or_else(|| Error::MissingObjectKey(".metadata.namespace"))?;

    // Prepare the input for calling reconcile_core
    let cr_api = Api::<K>::namespaced(client.clone(), &cr_ns);
    let get_cr_resp = cr_api.get(&cr_name).await;
    match get_cr_resp {
        Err(deps_hack::kube_client::error::Error::Api(ErrorResponse { reason, .. })) if &reason == "NotFound" => {
            println!("{} not found, end reconcile", cr_name);
            return Ok(Action::await_change());
        },
        Err(err) => {
            println!("Get cr failed with error: {}, will retry reconcile", err);
            return Ok(Action::requeue(Duration::from_secs(60)));
        },
        _ => {},
    }
    let cr = get_cr_resp.unwrap();
    println!("Get cr {}", deps_hack::k8s_openapi::serde_json::to_string(&cr).unwrap());

    let cr_wrapper = ResourceWrapperType::from_kube(cr);
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
        let (state_prime, req_option) = reconciler.reconcile_core(&cr_wrapper, resp_option, state);
        // Pattern match the request and send requests to the Kubernetes API via kube-rs methods
        match req_option {
            Option::Some(req) => match req {
                KubeAPIRequest::GetRequest(get_req) => {
                    let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                        client.clone(), get_req.namespace.as_rust_string_ref(), get_req.api_resource.as_kube_ref()
                    );
                    match api.get(get_req.name.as_rust_string_ref()).await {
                        std::result::Result::Err(err) => {
                            resp_option = Option::Some(KubeAPIResponse::GetResponse(
                                KubeGetResponse{
                                    res: vstd::result::Result::Err(kube_error_to_ghost(&err)),
                                }
                            ));
                            println!("Get failed with error: {}", err);
                        },
                        std::result::Result::Ok(obj) => {
                            resp_option = Option::Some(KubeAPIResponse::GetResponse(
                                KubeGetResponse{
                                    res: vstd::result::Result::Ok(DynamicObject::from_kube(obj)),
                                }
                            ));
                            println!("Get done");
                        },
                    }
                },
                KubeAPIRequest::CreateRequest(create_req) => {
                    let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                        client.clone(),
                        &create_req.obj.kube_metadata_ref().namespace.as_ref().unwrap(),
                        create_req.api_resource.as_kube_ref()
                    );
                    let pp = PostParams::default();
                    let obj_to_create = create_req.obj.into_kube();
                    match api.create(&pp, &obj_to_create).await {
                        std::result::Result::Err(err) => {
                            resp_option = Option::Some(KubeAPIResponse::CreateResponse(
                                KubeCreateResponse{
                                    res: vstd::result::Result::Err(kube_error_to_ghost(&err)),
                                }
                            ));
                            println!("Create failed with error: {}", err);
                        },
                        std::result::Result::Ok(obj) => {
                            resp_option = Option::Some(KubeAPIResponse::GetResponse(
                                KubeGetResponse{
                                    res: vstd::result::Result::Ok(DynamicObject::from_kube(obj)),
                                }
                            ));
                            println!("Create done");
                        },
                    }
                },
                _ => {
                    panic!("Not supported yet");
                }
            },
            _ => resp_option = Option::None,
        }
        state = state_prime;
    }

    return Ok(Action::requeue(Duration::from_secs(60)));
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
pub fn kube_error_to_ghost(error: &deps_hack::kube::Error) -> APIError {
    match error {
        deps_hack::kube::Error::Api(error_resp) => {
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
