use crate::v_replica_set_controller::exec::source::validator::validate_state;
use deps_hack::kube::core::{
    admission::{AdmissionRequest, AdmissionResponse, AdmissionReview},
    DynamicObject, ResourceExt,
};
use deps_hack::tracing::*;
use deps_hack::warp::{reply, Reply};
use std::convert::Infallible;

pub async fn validate_handler(
    body: AdmissionReview<DynamicObject>,
) -> Result<impl Reply, Infallible> {
    let req: AdmissionRequest<_> = match body.try_into() {
        Ok(r) => r,
        Err(err) => {
            error!("Format Error: {}", err.to_string());
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