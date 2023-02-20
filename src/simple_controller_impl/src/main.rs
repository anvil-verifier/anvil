// Nightly clippy (0.1.64) considers Drop a side effect, see https://github.com/rust-lang/rust-clippy/issues/9608
#![allow(clippy::unnecessary_lazy_evaluations)]

use anyhow::Result;
use futures::StreamExt;
use k8s_openapi::api::core::v1::ConfigMap;
use kube::{
    api::{Api, ListParams, ObjectMeta, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResource, CustomResourceExt,
};
use kube_client;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use thiserror::Error;
use tokio::time::Duration;
use tracing::*;

#[derive(Debug, Error)]
enum Error {
    #[error("MissingObjectKey: {0}")]
    MissingObjectKey(&'static str),
}

#[derive(CustomResource, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[kube(group = "anvil.dev", version = "v1", kind = "SimpleCR")]
#[kube(shortname = "cr", namespaced)]
struct SimpleCRSpec {
    pub content: String,
}

// The local state used in each reconcile core invocation
// It is very simple and only has a pc
struct SimpleReconcileState {
    pub reconcile_pc: i32,
}

// This is the key of the custom resource object that the controller is reconciling for
// TODO: add the type of the resource (i.e., kind) into it
#[derive(Clone)]
struct ResourceKey {
    name: String,
    namespace: String,
    // kind: String,
}

// This is the API request that reconcile_core returns to reconcile
// I did not find a way to encode the type into the enum
// so each request operation is hardcoded to one type
// This is a big limitation and we should work on it
enum APIRequest {
    GetCRReq(ResourceKey),
    CreateConfigMapReq(ConfigMap),
}

// The response that reconcile passes to reconcile_core
// It has the same problem as APIRequest
enum APIResponse {
    GetCRResp(kube_client::Result<SimpleCR>),
    CreateConfigMapResp(kube_client::Result<ConfigMap>),
}

// The initial state to start the reconcile_core loop in each reconcile invocation
fn reconcile_init_state() -> SimpleReconcileState {
    SimpleReconcileState { reconcile_pc: 0 }
}

// It says there is no more work from reconcile_core and reconcile should return OK
// TODO: we also need a function for returning Err
fn reconcile_done(state: &SimpleReconcileState) -> bool {
    state.reconcile_pc != 0 && state.reconcile_pc != 1
}

// This is the untrusted reconcile logic
// It takes (1) the key to the custom resource object, (2) the response of the previous request, and (3) the current reconcile state
// and returns (1) a new reconcile state and (2) a request to send to the Kubernetes API
// We start from simple and keep consistent with the simple reconcile spec by ignoring the response
fn reconcile_core(
    cr_key: &ResourceKey,
    resp_option: &Option<APIResponse>,
    state: &SimpleReconcileState,
) -> (SimpleReconcileState, Option<APIRequest>) {
    let pc = state.reconcile_pc;
    if pc == 0 {
        let state_prime = SimpleReconcileState { reconcile_pc: 1 };
        let req_option = Some(APIRequest::GetCRReq(cr_key.clone()));
        info!("Send request to get CR");
        (state_prime, req_option)
    } else if pc == 1 {
        let state_prime = SimpleReconcileState { reconcile_pc: 2 };
        let cm = ConfigMap {
            metadata: ObjectMeta {
                name: Some(cr_key.name.clone() + "-cm"),
                namespace: Some(cr_key.namespace.clone()),
                ..ObjectMeta::default()
            },
            data: None,
            ..Default::default()
        };
        let req_option = Some(APIRequest::CreateConfigMapReq(cm));
        info!("Send request to create configmap");
        (state_prime, req_option)
    } else {
        let state_prime = SimpleReconcileState {
            reconcile_pc: state.reconcile_pc,
        };
        info!("Should not reach here");
        (state_prime, None)
    }
}

// The reconcile function is called by the kube-rs framework
// All the reconcile logic is in the reconcile function
async fn reconcile(cr: Arc<SimpleCR>, ctx: Arc<Data>) -> Result<Action, Error> {
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
    let cr_key = ResourceKey {
        name: cr_name.clone(),
        namespace: cr_ns.clone(),
    };
    let mut state = reconcile_init_state();
    let mut resp_option: Option<APIResponse> = None;

    // Call reconcile_core in a loop
    loop {
        // If reconcile core is done, then breaks the loop
        if reconcile_done(&state) {
            break;
        }
        // Feed the current reconcile state and get the new state and the pending request
        let (state_prime, req_option) = reconcile_core(&cr_key, &resp_option, &state);
        // Pattern match the request and send requests to the Kubernetes API via kube-rs methods
        match req_option {
            Some(req) => match req {
                APIRequest::GetCRReq(key) => {
                    let cr_api = Api::<SimpleCR>::namespaced(client.clone(), &key.namespace);
                    resp_option = Some(APIResponse::GetCRResp(cr_api.get(&key.name).await));
                }
                APIRequest::CreateConfigMapReq(cm) => {
                    let cm_api = Api::<ConfigMap>::namespaced(
                        client.clone(),
                        cm.metadata
                            .namespace
                            .as_ref()
                            .ok_or_else(|| Error::MissingObjectKey(".metadata.namespace"))?,
                    );
                    let pp = PostParams::default();
                    resp_option = Some(APIResponse::CreateConfigMapResp(
                        cm_api.create(&pp, &cm).await,
                    ));
                }
            },
            _ => resp_option = None,
        }
        state = state_prime
    }

    Ok(Action::requeue(Duration::from_secs(100)))
}

// The controller triggers this on reconcile errors
fn error_policy(_object: Arc<SimpleCR>, _error: &Error, _ctx: Arc<Data>) -> Action {
    Action::requeue(Duration::from_secs(1))
}

// Data we want access to in error/reconcile calls
struct Data {
    client: Client,
}

// The main function registers the (1) the reconcile function and (2) the trigger of reconcile
#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let client = Client::try_default().await?;

    let crs = Api::<SimpleCR>::all(client.clone());

    println!(
        "Simple CRD:\n{}\n",
        serde_yaml::to_string(&SimpleCR::crd())?
    );

    info!("starting simple-controller");

    Controller::new(crs, ListParams::default()) // The controller's reconcile is triggered when a CR is created/updated
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { client })) // The reconcile function is registered
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => warn!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller terminated");
    Ok(())
}
