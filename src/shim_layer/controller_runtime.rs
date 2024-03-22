// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::exec::{api_method::*, dynamic::*, resource::*};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::shim_layer::fault_injection::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use core::hash::Hash;
use deps_hack::anyhow::Result;
use deps_hack::futures::{Future, Stream, StreamExt, TryFuture};
use deps_hack::kube::{
    api::{Api, DeleteParams, ListParams, ObjectMeta, PostParams, Resource},
    runtime::{
        controller::{self, Action, Controller},
        reflector, watcher,
    },
    Client, CustomResource, CustomResourceExt,
};
use deps_hack::kube_core::{ErrorResponse, NamespaceResourceScope};
use deps_hack::serde::{de::DeserializeOwned, Serialize};
use deps_hack::Error;
use std::sync::Arc;
use std::time::Duration;
use vstd::{string::*, view::*};

verus! {

// The shim layer connects the verified reconciler to the trusted kube-rs APIs.
// The key is to implement the reconcile function (impl FnMut(Arc<K>, Arc<Ctx>) -> ReconcilerFut),
// which is required by the kube-rs framework to build a controller,
// on top of reconcile_core, which is provided by the developer.

// run_controller prepares and runs the controller. It requires:
// K: the custom resource type
// ReconcilerType: the reconciler type
#[verifier(external)]
pub async fn run_controller<K, ReconcilerType>(fault_injection: bool) -> Result<()>
where
    K: Clone + Resource<Scope = NamespaceResourceScope> + CustomResourceExt + DeserializeOwned + Debug + Send + Serialize + Sync + 'static,
    K::DynamicType: Default + Eq + Hash + Clone + Debug + Unpin,
    ReconcilerType: Reconciler + Send + Sync + Default,
    ReconcilerType::R: ResourceWrapper<K> + Send,
    ReconcilerType::T: Send,
    <ReconcilerType::ExternalAPIType as ExternalAPIShimLayer>::Input: Send,
    <ReconcilerType::ExternalAPIType as ExternalAPIShimLayer>::Output: Send,
{
    let client = Client::try_default().await?;
    let crs = Api::<K>::all(client.clone());

    // Build the async closure on top of reconcile_with
    let reconcile = |cr: Arc<K>, ctx: Arc<Data>| async move {
        return reconcile_with::<K, ReconcilerType>(
            cr, ctx, fault_injection
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

// reconcile_with implements the reconcile function by repeatedly invoking ReconcilerType::reconcile_core.
// reconcile_with will be invoked by kube-rs whenever kube-rs's watcher receives any relevant event to the controller.
// In each invocation, reconcile_with invokes ReconcilerType::reconcile_core in a loop:
// it starts with ReconcilerType::reconcile_init_state, and in each iteration it invokes ReconcilerType::reconcile_core
// with the new state returned by the previous invocation.
// For each request from ReconcilerType::reconcile_core, it invokes kube-rs APIs to send the request to the Kubernetes API.
// It ends the loop when the ReconcilerType reports the reconcile is done (ReconcilerType::reconcile_done)
// or encounters error (ReconcilerType::reconcile_error).
#[verifier(external)]
pub async fn reconcile_with<K, ReconcilerType>(cr: Arc<K>, ctx: Arc<Data>, fault_injection: bool) -> Result<Action, Error>
where
    K: Clone + Resource<Scope = NamespaceResourceScope> + CustomResourceExt + DeserializeOwned + Debug + Serialize,
    K::DynamicType: Default + Clone + Debug,
    ReconcilerType: Reconciler,
    ReconcilerType::R: ResourceWrapper<K>,
{
    let client = &ctx.client;

    let cr_name = cr.meta().name.as_ref().ok_or_else(|| Error::ShimLayerError("Custom resource misses \".metadata.name\"".to_string()))?;
    let cr_namespace = cr.meta().namespace.as_ref().ok_or_else(|| Error::ShimLayerError("Custom resources misses \".metadata.namespace\"".to_string()))?;
    let cr_kind = K::kind(&K::DynamicType::default()).to_string();

    let cr_key = format!("{}/{}/{}", cr_kind, cr_namespace, cr_name);
    let log_header = format!("Reconciling {}:", cr_key);

    let cr_api = Api::<K>::namespaced(client.clone(), &cr_namespace);
    // Get the custom resource by a quorum read to Kubernetes' storage (etcd) to get the most updated custom resource
    let get_cr_resp = cr_api.get(&cr_name).await;
    match get_cr_resp {
        Err(deps_hack::kube_client::error::Error::Api(ErrorResponse { reason, .. })) if &reason == "NotFound" => {
            println!("{} Custom resource {} not found, end reconcile", log_header, cr_name);
            return Ok(Action::await_change());
        },
        Err(err) => {
            println!("{} Get custom resource {} failed with error: {}, will retry reconcile", log_header, cr_name, err);
            return Ok(Action::requeue(Duration::from_secs(60)));
        },
        _ => {},
    }
    // Wrap the custom resource with Verus-friendly wrapper type (which has a ghost version, i.e., view)
    let cr = get_cr_resp.unwrap();
    println!("{} Get cr {}", log_header, deps_hack::k8s_openapi::serde_json::to_string(&cr).unwrap());

    let cr_wrapper = ReconcilerType::R::from_kube(cr);
    let mut state = ReconcilerType::reconcile_init_state();
    let mut resp_option: Option<Response<<ReconcilerType::ExternalAPIType as ExternalAPIShimLayer>::Output>> = None;
    // check_fault_timing is only set to true right after the controller issues any create, update or delete request,
    // or external request
    let mut check_fault_timing: bool;

    // Call reconcile_core in a loop
    loop {
        check_fault_timing = false;
        // If reconcile core is done, then breaks the loop
        if ReconcilerType::reconcile_done(&state) {
            println!("{} done", log_header);
            break;
        }
        if ReconcilerType::reconcile_error(&state) {
            println!("{} error", log_header);
            return Err(Error::ReconcileCoreError);
        }
        // Feed the current reconcile state and get the new state and the pending request
        let (state_prime, request_option) = ReconcilerType::reconcile_core(&cr_wrapper, resp_option, state);
        // Pattern match the request and send requests to the Kubernetes API via kube-rs methods
        match request_option {
            Some(request) => match request {
                Request::KRequest(req) => {
                    let kube_resp: KubeAPIResponse;
                    match req {
                        KubeAPIRequest::GetRequest(get_req) => {
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(), get_req.namespace.as_rust_string_ref(), get_req.api_resource.as_kube_ref()
                            );
                            let key = get_req.key();
                            match api.get(get_req.name.as_rust_string_ref()).await {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::GetResponse(KubeGetResponse{
                                        res: Err(kube_error_to_ghost(&err)),
                                    });
                                    println!("{} Get {} failed with error: {}", log_header, key, err);
                                },
                                Ok(obj) => {
                                    kube_resp = KubeAPIResponse::GetResponse(KubeGetResponse{
                                        res: Ok(DynamicObject::from_kube(obj)),
                                    });
                                    println!("{} Get {} done", log_header, key);
                                },
                            }
                        },
                        KubeAPIRequest::ListRequest(list_req) => {
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(), list_req.namespace.as_rust_string_ref(), list_req.api_resource.as_kube_ref()
                            );
                            let key = list_req.key();
                            let lp = ListParams::default();
                            match api.list(&lp).await {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::ListResponse(KubeListResponse{
                                        res: Err(kube_error_to_ghost(&err)),
                                    });
                                    println!("{} List {} failed with error: {}", log_header, key, err);
                                },
                                Ok(obj_list) => {
                                    kube_resp = KubeAPIResponse::ListResponse(KubeListResponse{
                                        res: Ok(obj_list.items.into_iter().map(|obj| DynamicObject::from_kube(obj)).collect()),
                                    });
                                    println!("{} List {} done", log_header, key);
                                },
                            }
                        },
                        KubeAPIRequest::CreateRequest(create_req) => {
                            check_fault_timing = true;
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(), create_req.namespace.as_rust_string_ref(), create_req.api_resource.as_kube_ref()
                            );
                            let pp = PostParams::default();
                            let key = create_req.key();
                            let obj_to_create = create_req.obj.into_kube();
                            match api.create(&pp, &obj_to_create).await {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::CreateResponse(KubeCreateResponse{
                                        res: Err(kube_error_to_ghost(&err)),
                                    });
                                    println!("{} Create {} failed with error: {}", log_header, key, err);
                                },
                                Ok(obj) => {
                                    kube_resp = KubeAPIResponse::CreateResponse(KubeCreateResponse{
                                        res: Ok(DynamicObject::from_kube(obj)),
                                    });
                                    println!("{} Create {} done", log_header, key);
                                },
                            }
                        },
                        KubeAPIRequest::DeleteRequest(delete_req) => {
                            check_fault_timing = true;
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(), delete_req.namespace.as_rust_string_ref(), delete_req.api_resource.as_kube_ref()
                            );
                            let dp = DeleteParams::default();
                            let key = delete_req.key();
                            match api.delete(delete_req.name.as_rust_string_ref(), &dp).await {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::DeleteResponse(KubeDeleteResponse{
                                        res: Err(kube_error_to_ghost(&err)),
                                    });
                                    println!("{} Delete {} failed with error: {}", log_header, key, err);
                                },
                                Ok(_) => {
                                    kube_resp = KubeAPIResponse::DeleteResponse(KubeDeleteResponse{
                                        res: Ok(()),
                                    });
                                    println!("{} Delete {} done", log_header, key);
                                },
                            }
                        },
                        KubeAPIRequest::UpdateRequest(update_req) => {
                            check_fault_timing = true;
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(), update_req.namespace.as_rust_string_ref(), update_req.api_resource.as_kube_ref()
                            );
                            let pp = PostParams::default();
                            let key = update_req.key();
                            let obj_to_update = update_req.obj.into_kube();
                            match api.replace(update_req.name.as_rust_string_ref(), &pp, &obj_to_update).await {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::UpdateResponse(KubeUpdateResponse{
                                        res: Err(kube_error_to_ghost(&err)),
                                    });
                                    println!("{} Update {} failed with error: {}", log_header, key, err);
                                },
                                Ok(obj) => {
                                    kube_resp = KubeAPIResponse::UpdateResponse(KubeUpdateResponse{
                                        res: Ok(DynamicObject::from_kube(obj)),
                                    });
                                    println!("{} Update {} done", log_header, key);
                                },
                            }
                        },
                        KubeAPIRequest::UpdateStatusRequest(update_status_req) => {
                            check_fault_timing = true;
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(), update_status_req.namespace.as_rust_string_ref(), update_status_req.api_resource.as_kube_ref()
                            );
                            let pp = PostParams::default();
                            let key = update_status_req.key();
                            let obj_to_update = update_status_req.obj.into_kube();
                            // Here we assume serde_json always succeed
                            match api.replace_status(update_status_req.name.as_rust_string_ref(), &pp, deps_hack::k8s_openapi::serde_json::to_vec(&obj_to_update).unwrap()).await {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::UpdateStatusResponse(KubeUpdateStatusResponse{
                                        res: Err(kube_error_to_ghost(&err)),
                                    });
                                    println!("{} UpdateStatus {} failed with error: {}", log_header, key, err);
                                },
                                Ok(obj) => {
                                    kube_resp = KubeAPIResponse::UpdateStatusResponse(KubeUpdateStatusResponse{
                                        res: Ok(DynamicObject::from_kube(obj)),
                                    });
                                    println!("{} UpdateStatus {} done", log_header, key);
                                },
                            }
                        },
                    }
                    resp_option = Some(Response::KResponse(kube_resp));
                },
                Request::ExternalRequest(req) => {
                    check_fault_timing = true;
                    let external_resp = ReconcilerType::ExternalAPIType::call_external_api(req);
                    resp_option = Some(Response::ExternalResponse(external_resp));
                },
            },
            _ => resp_option = None,
        }
        if check_fault_timing && fault_injection {
            // If the controller just issues create, update, delete or external request,
            // and fault injection option is on, then check whether to crash at this point
            let result = crash_or_continue(client, &cr_key, &log_header).await;
            if result.is_err() {
                println!("{} crash_or_continue fails due to {}", log_header, result.unwrap_err());
            }
        }
        state = state_prime;
    }

    return Ok(Action::requeue(Duration::from_secs(60)));
}

// error_policy defines the controller's behavior when the reconcile ends with an error.
#[verifier(external)]
pub fn error_policy<K>(_object: Arc<K>, _error: &Error, _ctx: Arc<Data>) -> Action
where
    K: Clone + Resource + DeserializeOwned + Debug + Send + Sync + 'static,
    K::DynamicType: Eq + Hash + Clone + Debug + Unpin,
{
    Action::requeue(Duration::from_secs(10))
}

// Data is passed to reconcile_with.
// It carries the client that communicates with Kubernetes API.
#[verifier(external_body)]
pub struct Data {
    pub client: Client,
}

// kube_error_to_ghost translates the API error from kube-rs APIs
// to the form that can be processed by reconcile_core.

// TODO: match more error types.
#[verifier(external)]
pub fn kube_error_to_ghost(error: &deps_hack::kube::Error) -> APIError {
    match error {
        deps_hack::kube::Error::Api(error_resp) => {
            if &error_resp.reason == "NotFound" {
                APIError::ObjectNotFound
            } else if &error_resp.reason == "AlreadyExists" {
                APIError::ObjectAlreadyExists
            } else if &error_resp.reason == "BadRequest" {
                APIError::BadRequest
            } else if &error_resp.reason == "Conflict" {
                APIError::Conflict
            } else if &error_resp.reason == "Invalid" {
                APIError::Invalid
            } else if &error_resp.reason == "InternalError" {
                APIError::InternalError
            } else if &error_resp.reason == "Timeout" {
                APIError::Timeout
            } else if &error_resp.reason == "ServerTimeout" {
                APIError::ServerTimeout
            } else {
                APIError::Other
            }
        },
        _ => APIError::Other,
    }
}

}
