// Nightly clippy (0.1.64) considers Drop a side effect, see https://github.com/rust-lang/rust-clippy/issues/9608
#![allow(clippy::unnecessary_lazy_evaluations)]

use crate::fluent_types::*;

use anyhow::Result;
use k8s_openapi::api::core::v1::Secret;
use k8s_openapi::ByteString;
use kube::{
    api::{Api, PostParams},
    runtime::controller::Action,
    Client,
};
use kube_client;
use kube_core::{self, ObjectMeta};
use std::collections::BTreeMap;
use std::sync::Arc;
use tokio::time::Duration;
use tracing::*;

fn make_secret_name(fbc: &FluentBitConfig) -> String {
    fbc.metadata.name.as_ref().unwrap().clone()
}

// TODO(xudong): make the configuration actually configurable
fn make_secret(fbc: &FluentBitConfig) -> Secret {
    Secret {
        metadata: ObjectMeta {
            name: Some(make_secret_name(fbc)),
            namespace: fbc.metadata.namespace.clone(),
            ..ObjectMeta::default()
        },
        data: Some(BTreeMap::from([
            (
                "fluent-bit.conf".to_string(),
                ByteString(fbc.spec.config.clone().into_bytes()),
            ),
            (
                "parsers.conf".to_string(),
                ByteString("".to_string().into_bytes()),
            ),
        ])),
        ..Secret::default()
    }
}

async fn reconcile_secret(fbc: &FluentBitConfig, client: Client) -> Result<(), Error> {
    let secret_api =
        Api::<Secret>::namespaced(client.clone(), fbc.metadata.namespace.as_ref().unwrap());
    let secret = make_secret(&fbc);
    info!("Create secret: {}", secret.metadata.name.as_ref().unwrap());
    match secret_api.create(&PostParams::default(), &secret).await {
        Err(e) => match e {
            kube_client::Error::Api(kube_core::ErrorResponse { ref reason, .. })
                if reason.clone() == "AlreadyExists" =>
            {
                return Ok(())
            }
            _ => return Err(Error::ReconcileSecretFailed(e)),
        },
        _ => return Ok(()),
    }
}

// In the reference fluent-operator, there are multiple reconcile loops for manaing fluent-bit.
// One reconcile loop creates the configuration (the secret object) and the other one brings up the daemon set
// that requires the configuration data.
// Here we simplify the design and fold everything into one reconcile loop.
// TODO(xudong): implement multiple reconcile loops that coordinate with each other.
pub async fn fluent_bit_config_reconcile(
    fbc_from_cache: Arc<FluentBitConfig>,
    ctx: Arc<Data>,
) -> Result<Action, Error> {
    info!("FluentBitConfig reconciler running...");

    let client = &ctx.client;

    let fbc_name = fbc_from_cache
        .metadata
        .name
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.name"))?;
    let fbc_ns = fbc_from_cache
        .metadata
        .namespace
        .as_ref()
        .ok_or_else(|| Error::MissingObjectKey(".metadata.namespace"))?;

    let fbc_api = Api::<FluentBitConfig>::namespaced(client.clone(), &fbc_ns);

    // Get the FluentBitConfig custom resource before taking any reconciliation actions.
    let get_result = fbc_api.get(&fbc_name).await;
    match get_result {
        Err(kube_client::error::Error::Api(kube_core::ErrorResponse { reason, .. }))
            if &reason == "NotFound" =>
        {
            info!("{} not found, end reconcile", fbc_name);
            return Ok(Action::await_change());
        }
        Err(e) => return Err(Error::CRGetFailed(e)),
        _ => {}
    }
    let fbc = get_result.unwrap();

    // The secret contains the configuration data, including the input, filters and the output.
    // TODO(xudong): see whether we can use configmap here
    reconcile_secret(&fbc, client.clone()).await?;

    Ok(Action::requeue(Duration::from_secs(60)))
}

pub fn fluent_bit_config_error_policy(
    _object: Arc<FluentBitConfig>,
    error: &Error,
    _ctx: Arc<Data>,
) -> Action {
    warn!("Reconcile failed due to error: {}", error);
    Action::requeue(Duration::from_secs(10))
}
