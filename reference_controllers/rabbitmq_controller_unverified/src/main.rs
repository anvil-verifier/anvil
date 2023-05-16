#![allow(clippy::unnecessary_lazy_evaluations)]


pub mod rabbitmqcluster_types;

use anyhow::Result;
use futures::StreamExt;
use k8s_openapi::api::apps::v1 as appsv1;
use k8s_openapi::api::core::v1 as corev1;
use kube::{
    api::{Api, ListParams, PostParams},
    runtime::controller::{Action, Controller},
    Client, CustomResourceExt,
};
use kube_client;
use kube_core;
use std::{env, sync::Arc};
use thiserror::Error;
use tokio::time::Duration;
use tracing::*;

use crate::rabbitmqcluster_types::*;

fn main() {


    println!("Hello, world!");
}
