#![allow(unused_imports)]
#![allow(unused_variables)]
pub mod common;
pub mod rabbitmq_e2e;
pub mod vreplicaset_e2e;
pub mod vdeployment_e2e;
pub mod vstatefulset_e2e;
pub mod vstatefulset_admission_e2e;
pub mod vreplicaset_admission_e2e;
pub mod vdeployment_admission_e2e;

use common::Error;
use std::str::FromStr;
use std::{env, sync::Arc};
use tracing::*;
use rabbitmq_e2e::{rabbitmq_e2e_test, rabbitmq_ephemeral_e2e_test, rabbitmq_scaling_e2e_test};
use vreplicaset_e2e::vreplicaset_e2e_test;
use vreplicaset_admission_e2e::vreplicaset_admission_e2e_test;
use vdeployment_e2e::vdeployment_e2e_test;
use vdeployment_admission_e2e::vdeployment_admission_e2e_test;
use vstatefulset_e2e::vstatefulset_e2e_test;
use vstatefulset_admission_e2e::vstatefulset_admission_e2e_test;

#[tokio::main]
async fn main() -> Result<(), Error> {
    tracing_subscriber::fmt::init();

    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();
    match cmd.as_str() {
        "rabbitmq" => {
            info!("Running rabbitmq end-to-end test");
            return rabbitmq_e2e_test().await;
        }
        "rabbitmq-scaling" => {
            info!("Running rabbitmq end-to-end test for scaling");
            return rabbitmq_scaling_e2e_test().await;
        }
        "rabbitmq-ephemeral" => {
            info!("Running rabbitmq end-to-end test for ephemeral storage");
            return rabbitmq_ephemeral_e2e_test().await;
        }
        "vreplicaset" => {
            info!("Running vreplicaset end-to-end test");
            return vreplicaset_e2e_test().await;
        }
        "vdeployment" => {
            info!("Running vdeployment end-to-end test");
            return vdeployment_e2e_test().await;
        }
        "vstatefulset" => {
            info!("Running vstatefulset end-to-end test");
            return vstatefulset_e2e_test().await;
        }
        "vreplicaset-admission" => {
            info!("Running vreplicaset-admission end-to-end test");
            return vreplicaset_admission_e2e_test().await;
        }
        "vdeployment-admission" => {
            info!("Running vdeployment-admission end-to-end test");
            return vdeployment_admission_e2e_test().await;
        }
        "vstatefulset-admission" => {
            info!("Running vstatefulset-admission end-to-end test");
            return vstatefulset_admission_e2e_test().await;
        }
        _ => {
            error!("Wrong command. Please specify the correct e2e test workload.");
            Ok(())
        }
    }
}
