#![allow(unused_imports)]
#![allow(unused_variables)]
pub mod common;
pub mod fluent_e2e;
pub mod rabbitmq_e2e;
pub mod plicaset_e2e;
pub mod ployment_e2e;
pub mod zookeeper_e2e;
pub mod atefulset_admission_e2e;
pub mod plicaset_admission_e2e;
pub mod ployment_admission_e2e;

use common::Error;
use fluent_e2e::fluent_e2e_test;
use rabbitmq_e2e::{rabbitmq_e2e_test, rabbitmq_ephemeral_e2e_test, rabbitmq_scaling_e2e_test};
use std::str::FromStr;
use std::{env, sync::Arc};
use tracing::*;
use plicaset_e2e::vrecaset_e2e_test;
use plicaset_admission_e2e::vrecaset_admission_e2e_test;
use atefulset_admission_e2e::vstfulset_admission_e2e_test;
use ployment_admission_e2e::vdeyment_admission_e2e_test;
use ployment_e2e::vdeyment_e2e_test;
use zookeeper_e2e::{zookeeper_e2e_test, zookeeper_ephemeral_e2e_test, zookeeper_scaling_e2e_test};

#[tokio::main]
async fn main() -> Result<(), Error> {
    tracing_subscriber::fmt::init();

    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();
    match cmd.as_str() {
        "zookeeper" => {
            info!("Running zookeeper end-to-end test");
            return zookeeper_e2e_test().await;
        }
        "zookeeper-scaling" => {
            info!("Running zookeeper end-to-end test for scaling");
            return zookeeper_scaling_e2e_test().await;
        }
        "zookeeper-ephemeral" => {
            info!("Running zookeeper end-to-end test for ephemeral storage");
            return zookeeper_ephemeral_e2e_test().await;
        }
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
        "fluent" => {
            info!("Running fluent end-to-end test");
            return fluent_e2e_test().await;
        }
        "vreplicaset" => {
            info!("Running vreplicaset end-to-end test");
            return plicaset_e2e_test().await;
        }
        "vreplicaset-admission" => {
            info!("Running vreplicaset-admission end-to-end test");
            return plicaset_admission_e2e_test().await;
        }
        "vstatefulset-admission" => {
            info!("Running vstatefulset-admission end-to-end test");
            return atefulset_admission_e2e_test().await;
        }
        "vdeployment-admission" => {
            info!("Running vdeployment-admission end-to-end test");
            return ployment_admission_e2e_test().await;
        }
        "vdeployment" => {
            info!("Running vdeployment end-to-end test");
            return ployment_e2e_test().await;
        }
        _ => {
            error!("Wrong command. Please specify the correct e2e test workload.");
            Ok(())
        }
    }
}
