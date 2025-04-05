#![allow(unused_imports)]

pub mod external_api;
pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod reconciler;
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;
#[path = "controller_examples/v_replica_set_controller/mod.rs"]
pub mod v_replica_set_controller;
pub mod vstd_ext;

use crate::v_replica_set_controller::exec::validator::validate_state;
use deps_hack::anyhow::Result;
use deps_hack::kube::CustomResourceExt;
use deps_hack::serde_yaml;
use deps_hack::tokio;
// use deps_hack::tracing::{error, info};
use deps_hack::tracing_subscriber;
use shim_layer::controller_runtime::run_controller;
use std::env;

use deps_hack::kube::core::{
    admission::{AdmissionRequest, AdmissionResponse, AdmissionReview},
    DynamicObject, ResourceExt,
};
use deps_hack::tracing::*;
use deps_hack::warp;
use deps_hack::warp::{reply, Filter, Reply};
use std::convert::Infallible;

pub async fn validate_handler(
    body: AdmissionReview<DynamicObject>,
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
        res = match validate_state(res.clone(), &obj) {
            Ok(res) => {
                info!("accepted: {:?} on resource {}", req.operation, name);
                res
            }
            Err(err) => {
                warn!("denied: {:?} on {} ({})", req.operation, name, err);
                res.deny(err.to_string())
            }
        };
    };
    Ok(reply::json(&res.into_review()))
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    let routes = warp::path("validate")
        .and(warp::body::json())
        .and_then(validate_handler)
        .with(warp::trace::request());

    warp::serve(warp::post().and(routes))
        .tls()
        .cert_path("/certs/tls.crt")
        .key_path("/certs/tls.key")
        .run(([0, 0, 0, 0], 8443))
        .await;
}
