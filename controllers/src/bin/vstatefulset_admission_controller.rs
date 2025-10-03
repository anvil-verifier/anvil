#![allow(unused_imports)]

use controllers::crds::*;
use verifiable_controllers::kubernetes_api_objects::exec::{dynamic::DynamicObject, resource::ResourceWrapper};
use controllers::vstatefulset_controller::trusted::exec_types::VStatefulSet;
use anyhow::Result;
use kube::core::{
    admission::{AdmissionRequest, AdmissionResponse, AdmissionReview},
    DynamicObject as KubeDynamicObject, ResourceExt,
};
use kube::CustomResourceExt;
use serde_yaml;
use tokio;
use tracing::*;
use tracing_subscriber;
use warp::*;
use verifiable_controllers::shim_layer::controller_runtime::run_controller;
use std::convert::Infallible;
use std::env;
use std::error::Error;

pub fn validate_state(vss: &VStatefulSet) -> Result<(), String> {
    // Call executable state validation
    if vss.state_validation() {
        Ok(())
    } else {
        Err("Invalid VStatefulSet".to_string())
    }
}

pub async fn validate_handler(
    body: AdmissionReview<KubeDynamicObject>,
) -> Result<impl Reply, Infallible> {
    let req: AdmissionRequest<_> = match body.try_into() {
        Ok(req) => req,
        Err(err) => {
            error!("invalid request: {}", err.to_string());
            return Ok(reply::json(
                &AdmissionResponse::invalid(err.to_string()).into_review(),
            ));
        }
    };

    let mut res = AdmissionResponse::from(&req);
    if let Some(obj) = req.object {
        let name = obj.name_any();
        let local_obj = DynamicObject::from_kube(obj.clone());

        // Use unmarshal function to convert DynamicObject to VStatefulSet
        let vsts_result = VStatefulSet::unmarshal(local_obj);
        if let Ok(vsts) = vsts_result {
            res = match validate_state(&vsts) {
                Ok(()) => {
                    info!("accepted: {:?} on resource {}", req.operation, name);
                    res
                }
                Err(err) => {
                    warn!("denied: {:?} on {} ({})", req.operation, name, err);
                    res.deny(err.to_string())
                }
            };
        } else {
            warn!("Failed to unmarshal VStatefulSet");
            res = res.deny("Failed to unmarshal VStatefulSet".to_string());
        }
    };
    Ok(reply::json(&res.into_review()))
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    let routes = path("validate")
        .and(body::json())
        .and_then(validate_handler)
        .with(trace::request());

    serve(post().and(routes))
        .tls()
        .cert_path("/certs/tls.crt")
        .key_path("/certs/tls.key")
        .run(([0, 0, 0, 0], 8443))
        .await;
}
