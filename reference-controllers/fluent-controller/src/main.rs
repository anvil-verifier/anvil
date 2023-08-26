// Nightly clippy (0.1.64) considers Drop a side effect, see https://github.com/rust-lang/rust-clippy/issues/9608
#![allow(clippy::unnecessary_lazy_evaluations)]

pub mod fluent_bit_config_reconciler;
pub mod fluent_bit_reconciler;
pub mod fluent_types;

use anyhow::Result;
use futures::StreamExt;
use kube::{
    api::{Api, ListParams},
    runtime::{
        controller::{self, Action, Controller},
        reflector::ObjectRef,
    },
    Client, CustomResourceExt, Resource,
};
use std::{env, sync::Arc};
use tracing::*;

use crate::fluent_bit_config_reconciler::*;
use crate::fluent_bit_reconciler::*;
use crate::fluent_types::*;

pub fn report_controller_reconciled<K, QueueErr>(
    controller_name: &str,
    result: &Result<(ObjectRef<K>, Action), controller::Error<Error, QueueErr>>,
) where
    K: Resource,
    QueueErr: std::error::Error,
{
    match result {
        Ok((obj, _)) => {
            tracing::info!(
                controller.name = controller_name,
                object = %obj,
                "Reconciled object"
            );
        }
        Err(err) => {
            tracing::error!(
                controller.name = controller_name,
                error = err as &dyn std::error::Error,
                "Failed to reconcile object",
            );
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();
    if cmd == String::from("export") {
        info!("exporting custom resource definition");
        println!("{}", serde_yaml::to_string(&FluentBit::crd())?);
        println!("{}", serde_yaml::to_string(&FluentBitConfig::crd())?);
    } else if cmd == String::from("run") {
        info!("running fluent-controller");
        let client = Client::try_default().await?;
        let fb_api = Api::<FluentBit>::all(client.clone());
        let fbc_api = Api::<FluentBitConfig>::all(client.clone());

        let fb_reconciler = Controller::new(fb_api, ListParams::default())
            .shutdown_on_signal()
            .run(
                fluent_bit_reconcile,
                fluent_bit_error_policy,
                Arc::new(Data {
                    client: client.clone(),
                }),
            )
            .map(|res| report_controller_reconciled("fluent-bit-reconciler", &res));
        let fbc_reconciler = Controller::new(fbc_api, ListParams::default())
            .shutdown_on_signal()
            .run(
                fluent_bit_config_reconcile,
                fluent_bit_config_error_policy,
                Arc::new(Data {
                    client: Client::try_default().await?,
                }),
            )
            .map(|res| report_controller_reconciled("fluent-bit-config-reconciler", &res));
        futures::stream::select(fb_reconciler, fbc_reconciler)
            .collect::<()>()
            .await;
        info!("controller terminated");
    } else {
        warn!("wrong command; please use \"export\" or \"run\"");
    }
    Ok(())
}
