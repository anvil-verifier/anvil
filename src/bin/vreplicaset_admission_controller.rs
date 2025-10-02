#![allow(unused_imports)]
#[path = "vreplicaset_controller/mod.rs"]
pub mod vreplicaset_controller;

pub mod crds;

use crds::*;
use verifiable_controllers::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::vreplicaset_controller::trusted::exec_types::{VReplicaSet, VReplicaSetSpec};
use anyhow::Result;
use kube::CustomResourceExt;
use serde_yaml;
use tokio;
// use tracing::{error, info};
use verifiable_controllers::kubernetes_api_objects::exec::resource::ResourceWrapper;
use kube::core::{
    admission::{AdmissionRequest, AdmissionResponse, AdmissionReview},
    DynamicObject as KubeDynamicObject, ResourceExt,
};
use tracing::*;
use tracing_subscriber;
use warp::*;
use verifiable_controllers::shim_layer::controller_runtime::run_controller;
use std::env;
// use warp::{reply, Filter, Reply};
use std::convert::Infallible;
use std::error::Error;

pub fn validate_state(vrs: &VReplicaSet) -> Result<(), String> {
    // Call executable state validation
    if vrs.state_validation() {
        Ok(())
    } else {
        Err("Invalid VReplicaset".to_string())
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

        // Use unmarshal function to convert DynamicObject to VReplicaSet
        let vrs_result = VReplicaSet::unmarshal(local_obj);
        if let Ok(vrs) = vrs_result {
            res = match validate_state(&vrs) {
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
            warn!("Failed to unmarshal VReplicaSet");
            res = res.deny("Failed to unmarshal VReplicaSet".to_string());
        }
        // if vrs_result.is_err() {
        //     res.deny("Failed to unmarshal VReplicaSet".to_string())
        // }

        // // Get the VReplicaSet instance and its spec
        // let vrs = vrs_result.unwrap();
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
