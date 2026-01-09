use crate::external_shim_layer::*;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::exec::prelude::Preconditions;
use crate::kubernetes_api_objects::exec::{api_method::*, dynamic::*, resource::*};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::shim_layer::fault_injection::*;
use core::fmt::Debug;
use core::hash::Hash;
use deps_hack::anyhow::Result;
use deps_hack::futures::StreamExt;
use deps_hack::k8s_openapi::api::core::v1::{PersistentVolumeClaim, Pod};
use deps_hack::kube::{
    api::{Api, DeleteParams, ListParams, PostParams, Resource},
    runtime::{
        controller::{Action, Controller},
        watcher,
    },
    Client, CustomResourceExt,
};
use deps_hack::kube_core::{ErrorResponse, NamespaceResourceScope};
use deps_hack::serde::{de::DeserializeOwned, Serialize};
use deps_hack::tracing::{error, info, warn};
use deps_hack::Error;
use std::sync::Arc;
use std::time::Duration;
use vstd::string::*;

// The shim layer connects the verified reconciler to the trusted kube-rs APIs.
// The key is to implement the reconcile function (impl FnMut(Arc<K>, Arc<Ctx>) -> ReconcilerFut),
// which is required by the kube-rs framework to build a controller,
// on top of reconcile_core, which is provided by the developer.

// run_controller prepares and runs the controller. It requires:
// K: the custom resource type
// R: the reconciler type
pub async fn run_controller<K, R, E>(fault_injection: bool) -> Result<()>
where
    K: Clone
        + Resource<Scope = NamespaceResourceScope>
        + CustomResourceExt
        + DeserializeOwned
        + Debug
        + Send
        + Serialize
        + Sync
        + 'static,
    K::DynamicType: Default + Eq + Hash + Clone + Debug + Unpin,
    R: Reconciler + Send + Sync,
    R::K: ResourceWrapper<K> + Send,
    <R::K as View>::V: CustomResourceView,
    R::S: Send,
    R::EReq: Send,
    R::EResp: Send,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    let client = Client::try_default().await?;
    let crs = Api::<K>::all(client.clone());

    // Build the async closure on top of reconcile_with
    let reconcile = |cr: Arc<K>, ctx: Arc<Data>| async move {
        return reconcile_with::<K, R, E>(cr, ctx, fault_injection).await;
    };

    info!("starting controller");
    Controller::new(crs, watcher::Config::default()) // The controller's reconcile is triggered when a CR is created/updated
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { client })) // The reconcile function is registered
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => info!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller terminated");
    Ok(())
}

pub async fn run_controller_watching_owned<K, R, E>(fault_injection: bool) -> Result<()>
where
    K: Clone
        + Resource<Scope = NamespaceResourceScope>
        + CustomResourceExt
        + DeserializeOwned
        + Debug
        + Send
        + Serialize
        + Sync
        + 'static,
    K::DynamicType: Default + Eq + Hash + Clone + Debug + Unpin,
    R: Reconciler + Send + Sync,
    R::K: ResourceWrapper<K> + Send,
    <R::K as View>::V: CustomResourceView,
    R::S: Send,
    R::EReq: Send,
    R::EResp: Send,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    let client = Client::try_default().await?;
    let crs = Api::<K>::all(client.clone());

    // Build the async closure on top of reconcile_with
    let reconcile = |cr: Arc<K>, ctx: Arc<Data>| async move {
        return reconcile_with::<K, R, E>(cr, ctx, fault_injection).await;
    };

    info!("starting controller");
    Controller::new(crs, watcher::Config::default()) // The controller's reconcile is triggered when a CR is created/updated
        .owns(Api::<Pod>::all(client.clone()), watcher::Config::default()) // Watch owned Pods
        .owns(
            Api::<PersistentVolumeClaim>::all(client.clone()),
            watcher::Config::default(),
        ) // Watch owned PersistentVolumeClaims
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { client })) // The reconcile function is registered
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => info!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller terminated");
    Ok(())
}

// reconcile_with implements the reconcile function by repeatedly invoking R::reconcile_core.
// reconcile_with will be invoked by kube-rs whenever kube-rs's watcher receives any relevant event to the controller.
// In each invocation, reconcile_with invokes R::reconcile_core in a loop:
// it starts with R::reconcile_init_state, and in each iteration it invokes R::reconcile_core
// with the new state returned by the previous invocation.
// For each request from R::reconcile_core, it invokes kube-rs APIs to send the request to the Kubernetes API.
// It ends the loop when the R reports the reconcile is done (R::reconcile_done)
// or encounters error (R::reconcile_error).
pub async fn reconcile_with<K, R, E>(
    cr: Arc<K>,
    ctx: Arc<Data>,
    fault_injection: bool,
) -> Result<Action, Error>
where
    K: Clone
        + Resource<Scope = NamespaceResourceScope>
        + CustomResourceExt
        + DeserializeOwned
        + Debug
        + Serialize,
    K::DynamicType: Default + Clone + Debug,
    R: Reconciler,
    R::K: ResourceWrapper<K>,
    <R::K as View>::V: CustomResourceView,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    let client = &ctx.client;

    let cr_name = cr.meta().name.as_ref().ok_or_else(|| {
        Error::ShimLayerError("Custom resource misses \".metadata.name\"".to_string())
    })?;
    let cr_namespace = cr.meta().namespace.as_ref().ok_or_else(|| {
        Error::ShimLayerError("Custom resources misses \".metadata.namespace\"".to_string())
    })?;
    let cr_kind = K::kind(&K::DynamicType::default()).to_string();

    let cr_key = format!("{}/{}/{}", cr_kind, cr_namespace, cr_name);
    let log_header = format!("Reconciling {}:", cr_key);

    let cr_api = Api::<K>::namespaced(client.clone(), &cr_namespace);
    // Get the custom resource by a quorum read to Kubernetes' storage (etcd) to get the most updated custom resource
    let get_cr_resp = cr_api.get(&cr_name).await;
    match get_cr_resp {
        Err(deps_hack::kube_client::error::Error::Api(ErrorResponse { reason, .. }))
            if &reason == "NotFound" =>
        {
            warn!(
                "{} Custom resource {} not found, end reconcile",
                log_header, cr_name
            );
            return Ok(Action::await_change());
        }
        Err(err) => {
            warn!(
                "{} Get custom resource {} failed with error: {}, will retry reconcile",
                log_header, cr_name, err
            );
            return Ok(Action::requeue(Duration::from_secs(60)));
        }
        _ => {}
    }
    // Wrap the custom resource with Verus-friendly wrapper type (which has a ghost version, i.e., view)
    let cr = get_cr_resp.unwrap();
    info!(
        "{} Get cr {}",
        log_header,
        deps_hack::k8s_openapi::serde_json::to_string(&cr).unwrap()
    );

    let cr_wrapper = R::K::from_kube(cr);
    let mut state = R::reconcile_init_state();
    let mut resp_option: Option<Response<R::EResp>> = None;
    // check_fault_timing is only set to true right after the controller issues any create, update or delete request,
    // or external request
    let mut check_fault_timing: bool;

    // Call reconcile_core in a loop
    loop {
        check_fault_timing = false;
        // If reconcile core is done, then breaks the loop
        if R::reconcile_done(&state) {
            info!("{} done", log_header);
            break;
        }
        if R::reconcile_error(&state) {
            warn!("{} error", log_header);
            return Err(Error::ReconcileCoreError);
        }
        // Feed the current reconcile state and get the new state and the pending request
        let (state_prime, request_option) = R::reconcile_core(&cr_wrapper, resp_option, state);
        // Pattern match the request and send requests to the Kubernetes API via kube-rs methods
        match request_option {
            Some(request) => match request {
                Request::KRequest(req) => {
                    let kube_resp: KubeAPIResponse;
                    match req {
                        KubeAPIRequest::GetRequest(get_req) => {
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(),
                                &get_req.namespace,
                                get_req.api_resource.as_kube_ref(),
                            );
                            let key = get_req.key();
                            match api.get(&get_req.name).await {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::GetResponse(KubeGetResponse {
                                        res: Err(kube_error_to_api_error(&err)),
                                    });
                                    info!("{} Get {} failed with error: {}", log_header, key, err);
                                }
                                Ok(obj) => {
                                    kube_resp = KubeAPIResponse::GetResponse(KubeGetResponse {
                                        res: Ok(DynamicObject::from_kube(obj)),
                                    });
                                    info!("{} Get {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::ListRequest(list_req) => {
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(),
                                &list_req.namespace,
                                list_req.api_resource.as_kube_ref(),
                            );
                            let key = list_req.key();
                            let lp = ListParams::default();
                            match api.list(&lp).await {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::ListResponse(KubeListResponse {
                                        res: Err(kube_error_to_api_error(&err)),
                                    });
                                    info!("{} List {} failed with error: {}", log_header, key, err);
                                }
                                Ok(obj_list) => {
                                    kube_resp = KubeAPIResponse::ListResponse(KubeListResponse {
                                        res: Ok(obj_list
                                            .items
                                            .into_iter()
                                            .map(|obj| DynamicObject::from_kube(obj))
                                            .collect()),
                                    });
                                    info!("{} List {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::CreateRequest(create_req) => {
                            check_fault_timing = true;
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(),
                                &create_req.namespace,
                                create_req.api_resource.as_kube_ref(),
                            );
                            let pp = PostParams::default();
                            let key = create_req.key();
                            let obj_to_create = create_req.obj.into_kube();
                            match api.create(&pp, &obj_to_create).await {
                                Err(err) => {
                                    kube_resp =
                                        KubeAPIResponse::CreateResponse(KubeCreateResponse {
                                            res: Err(kube_error_to_api_error(&err)),
                                        });
                                    info!(
                                        "{} Create {} failed with error: {}",
                                        log_header, key, err
                                    );
                                }
                                Ok(obj) => {
                                    kube_resp =
                                        KubeAPIResponse::CreateResponse(KubeCreateResponse {
                                            res: Ok(DynamicObject::from_kube(obj)),
                                        });
                                    info!("{} Create {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::DeleteRequest(delete_req) => {
                            check_fault_timing = true;
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(),
                                &delete_req.namespace,
                                delete_req.api_resource.as_kube_ref(),
                            );
                            let mut dp = DeleteParams::default();
                            if delete_req.preconditions.is_some() {
                                dp = dp.preconditions(
                                    delete_req.preconditions.clone().unwrap().into_kube(),
                                );
                            }
                            let key = delete_req.key();
                            match api.delete(&delete_req.name, &dp).await {
                                Err(err) => {
                                    kube_resp =
                                        KubeAPIResponse::DeleteResponse(KubeDeleteResponse {
                                            res: Err(kube_error_to_api_error(&err)),
                                        });
                                    info!(
                                        "{} Delete {} failed with error: {}",
                                        log_header, key, err
                                    );
                                }
                                Ok(_) => {
                                    kube_resp =
                                        KubeAPIResponse::DeleteResponse(KubeDeleteResponse {
                                            res: Ok(()),
                                        });
                                    info!("{} Delete {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::UpdateRequest(update_req) => {
                            check_fault_timing = true;
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(),
                                &update_req.namespace,
                                update_req.api_resource.as_kube_ref(),
                            );
                            let pp = PostParams::default();
                            let key = update_req.key();
                            let obj_to_update = update_req.obj.into_kube();
                            match api.replace(&update_req.name, &pp, &obj_to_update).await {
                                Err(err) => {
                                    kube_resp =
                                        KubeAPIResponse::UpdateResponse(KubeUpdateResponse {
                                            res: Err(kube_error_to_api_error(&err)),
                                        });
                                    info!(
                                        "{} Update {} failed with error: {}",
                                        log_header, key, err
                                    );
                                }
                                Ok(obj) => {
                                    kube_resp =
                                        KubeAPIResponse::UpdateResponse(KubeUpdateResponse {
                                            res: Ok(DynamicObject::from_kube(obj)),
                                        });
                                    info!("{} Update {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::UpdateStatusRequest(update_status_req) => {
                            check_fault_timing = true;
                            let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                                client.clone(),
                                &update_status_req.namespace,
                                update_status_req.api_resource.as_kube_ref(),
                            );
                            let pp = PostParams::default();
                            let key = update_status_req.key();
                            let obj_to_update = update_status_req.obj.into_kube();
                            // Here we assume serde_json always succeed
                            match api
                                .replace_status(
                                    &update_status_req.name,
                                    &pp,
                                    deps_hack::k8s_openapi::serde_json::to_vec(&obj_to_update)
                                        .unwrap(),
                                )
                                .await
                            {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::UpdateStatusResponse(
                                        KubeUpdateStatusResponse {
                                            res: Err(kube_error_to_api_error(&err)),
                                        },
                                    );
                                    info!(
                                        "{} UpdateStatus {} failed with error: {}",
                                        log_header, key, err
                                    );
                                }
                                Ok(obj) => {
                                    kube_resp = KubeAPIResponse::UpdateStatusResponse(
                                        KubeUpdateStatusResponse {
                                            res: Ok(DynamicObject::from_kube(obj)),
                                        },
                                    );
                                    info!("{} UpdateStatus {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::GetThenDeleteRequest(req) => {
                            check_fault_timing = true;
                            kube_resp = KubeAPIResponse::GetThenDeleteResponse(
                                transactional_get_then_delete_by_retry(
                                    client,
                                    req,
                                    log_header.clone(),
                                )
                                .await,
                            );
                        }
                        KubeAPIRequest::GetThenUpdateRequest(req) => {
                            check_fault_timing = true;
                            kube_resp = KubeAPIResponse::GetThenUpdateResponse(
                                transactional_get_then_update_by_retry(
                                    client,
                                    req,
                                    log_header.clone(),
                                )
                                .await,
                            );
                        }
                    }
                    resp_option = Some(Response::KResponse(kube_resp));
                }
                Request::ExternalRequest(external_req) => {
                    check_fault_timing = true;
                    let external_resp = E::external_call(external_req);
                    resp_option = Some(Response::ExternalResponse(external_resp));
                }
            },
            _ => resp_option = None,
        }
        if check_fault_timing && fault_injection {
            // If the controller just issues create, update, delete or external request,
            // and fault injection option is on, then check whether to crash at this point
            let result = crash_or_continue(client, &cr_key, &log_header).await;
            if result.is_err() {
                error!(
                    "{} crash_or_continue fails due to {}",
                    log_header,
                    result.unwrap_err()
                );
            }
        }
        state = state_prime;
    }

    return Ok(Action::requeue(Duration::from_secs(60)));
}

// transactional_get_then_delete_by_retry retries get and then delete upon conflict errors to simulate atomic operations.
// This guarantees that the entire get_then_delete operation will not fail due to conflicts between concurrent
// controllers. Note that transactional_get_then_delete_by_retry's termination depends on fairness assumptions.
pub async fn transactional_get_then_delete_by_retry(
    client: &Client,
    req: KubeGetThenDeleteRequest,
    log_header: String,
) -> KubeGetThenDeleteResponse {
    // sanity check, can be removed if type invariant is supported by Verus
    let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
        client.clone(),
        &req.namespace,
        req.api_resource.as_kube_ref(),
    );
    let key = req.key();

    loop {
        // Step 1: get the object
        let get_result = api.get(&req.name).await;
        if let Err(err) = get_result {
            info!(
                "{} Get of Get-then-Delete {} failed with error: {}",
                log_header, key, err
            );
            return KubeGetThenDeleteResponse {
                res: Err(kube_error_to_api_error(&err)),
            };
        }
        // Step 2: if the object exists, perform a check using a predicate on object
        // The predicate: Is the current object owned by req.owner_ref?
        // TODO: the predicate should be provided by clients instead of the hardcoded one
        let current_obj = DynamicObject::from_kube(get_result.unwrap());
        if !current_obj
            .metadata()
            .owner_references_contains(&req.owner_ref)
        {
            return KubeGetThenDeleteResponse {
                res: Err(APIError::TransactionAbort),
            };
        }
        // Step 3: if the check passes, delete the object with a precondition
        // Note that resource_version and uid comes from the current object to avoid conflict error
        let dp = DeleteParams::default().preconditions(deps_hack::kube::api::Preconditions {
            resource_version: current_obj.as_kube_ref().metadata.resource_version.clone(),
            uid: current_obj.as_kube_ref().metadata.uid.clone(),
        });
        match api.delete(&req.name, &dp).await {
            Err(err) => {
                let api_err = kube_error_to_api_error(&err);
                match api_err {
                    APIError::Conflict => {
                        // Retry upon a conflict error
                        info!(
                            "{} Delete of Get-then-Delete {} failed with Conflict; retry...",
                            log_header, key
                        );
                        continue;
                    }
                    _ => {
                        info!(
                            "{} Delete of Get-then-Delete {} failed with error: {}",
                            log_header, key, err
                        );
                        return KubeGetThenDeleteResponse { res: Err(api_err) };
                    }
                }
            }
            Ok(obj) => {
                info!("{} Delete {} done", log_header, key);
                return KubeGetThenDeleteResponse { res: Ok(()) };
            }
        }
    }
}

// transactional_get_then_update_by_retry retries get and then update upon conflict errors to simulate atomic operations.
// This guarantees that the entire get_then_update operation will not fail due to conflicts between concurrent
// controllers. Note that transactional_get_then_update_by_retry's termination depends on fairness assumptions.
pub async fn transactional_get_then_update_by_retry(
    client: &Client,
    req: KubeGetThenUpdateRequest,
    log_header: String,
) -> KubeGetThenUpdateResponse {
    // sanity check, can be removed if type invariant is supported by Verus
    let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
        client.clone(),
        &req.namespace,
        req.api_resource.as_kube_ref(),
    );
    let pp = PostParams::default();
    let key = req.key();
    let mut obj_to_update = req.obj.into_kube();

    loop {
        // Step 1: get the object
        let get_result = api.get(&req.name).await;
        if let Err(err) = get_result {
            info!(
                "{} Get of Get-then-Update {} failed with error: {}",
                log_header, key, err
            );
            return KubeGetThenUpdateResponse {
                res: Err(kube_error_to_api_error(&err)),
            };
        }
        // Step 2: if the object exists, perform a check using a predicate on object
        // The predicate: Is the current object owned by req.owner_ref?
        // TODO: the predicate should be provided by clients instead of the hardcoded one
        let current_obj = DynamicObject::from_kube(get_result.unwrap());
        if !current_obj
            .metadata()
            .owner_references_contains(&req.owner_ref)
        {
            return KubeGetThenUpdateResponse {
                res: Err(APIError::TransactionAbort),
            };
        }
        // Step 3: if the check passes, overwrite the object with the new one
        // Note that resource_version and uid comes from the current object to avoid conflict error
        obj_to_update.metadata.uid = current_obj.as_kube_ref().metadata.uid.clone();
        obj_to_update.metadata.resource_version =
            current_obj.as_kube_ref().metadata.resource_version.clone();
        match api.replace(&req.name, &pp, &obj_to_update).await {
            Err(err) => {
                let api_err = kube_error_to_api_error(&err);
                match api_err {
                    APIError::Conflict => {
                        // Retry upon a conflict error
                        info!(
                            "{} Update of Get-then-Update {} failed with Conflict; retry...",
                            log_header, key
                        );
                        continue;
                    }
                    _ => {
                        info!(
                            "{} Update of Get-then-Update {} failed with error: {}",
                            log_header, key, err
                        );
                        return KubeGetThenUpdateResponse { res: Err(api_err) };
                    }
                }
            }
            Ok(obj) => {
                info!("{} Update {} done", log_header, key);
                return KubeGetThenUpdateResponse {
                    res: Ok(DynamicObject::from_kube(obj)),
                };
            }
        }
    }
}

// error_policy defines the controller's behavior when the reconcile ends with an error.
pub fn error_policy<K>(_object: Arc<K>, _error: &Error, _ctx: Arc<Data>) -> Action
where
    K: Clone + Resource + DeserializeOwned + Debug + Send + Sync + 'static,
    K::DynamicType: Eq + Hash + Clone + Debug + Unpin,
{
    Action::requeue(Duration::from_secs(10))
}

// Data is passed to reconcile_with.
// It carries the client that communicates with Kubernetes API.
pub struct Data {
    pub client: Client,
}

// kube_error_to_api_error translates the API error from kube-rs APIs
// to the form that can be processed by reconcile_core.

// TODO: match more error types.
pub fn kube_error_to_api_error(error: &deps_hack::kube::Error) -> APIError {
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
        }
        _ => APIError::Other,
    }
}
