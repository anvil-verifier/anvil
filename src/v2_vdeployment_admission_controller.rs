#![allow(unused_imports)]

#[path = "v2/external_shim_layer/mod.rs"]
pub mod external_shim_layer;
pub mod kubernetes_api_objects;
#[path = "v2/kubernetes_cluster/mod.rs"]
pub mod kubernetes_cluster;
#[path = "v2/reconciler/mod.rs"]
pub mod reconciler;
#[path = "v2/shim_layer/mod.rs"]
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;
#[path = "v2/controllers/vdeployment_controller/mod.rs"]
pub mod vdeployment_controller;
pub mod vstd_ext;

use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::vdeployment_controller::{
    exec::validator::validate_state, trusted::exec_types::VDeployment,
};
use deps_hack::anyhow::Result;
use deps_hack::kube::CustomResourceExt;
use deps_hack::serde_yaml;
use deps_hack::tokio;
// use deps_hack::tracing::{error, info};
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use deps_hack::kube::core::{
    admission::{AdmissionRequest, AdmissionResponse, AdmissionReview},
    DynamicObject as KubeDynamicObject, ResourceExt,
};
use deps_hack::tracing::*;
use deps_hack::tracing_subscriber;
use deps_hack::warp::*;
use shim_layer::controller_runtime::run_controller;
use std::env;
// use deps_hack::warp::{reply, Filter, Reply};
use std::convert::Infallible;

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

        // Use unmarshal function to convert DynamicObject to VDeployment
        let vdeploy_result = VDeployment::unmarshal(local_obj);
        if let Ok(vdeploy) = vdeploy_result {
            res = match validate_state(&vdeploy) {
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
            warn!("Failed to unmarshal VDeployment");
            res = res.deny("Failed to unmarshal VDeployment".to_string());
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