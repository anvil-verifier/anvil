// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use deps_hack::anyhow::Result;
use deps_hack::futures::{Future, Stream, StreamExt, TryFuture};
use deps_hack::k8s_openapi::api::core::v1::ConfigMap;
use deps_hack::kube::{
    api::{Api, ObjectMeta, PostParams, Resource},
    Client,
};
use deps_hack::Error;

verus! {

#[verifier(external)]
pub async fn crash_or_continue(client: &Client) -> Result<(), Error> {
    let config_map_name = "fault-injection-config";
    let config_map_api = Api::<ConfigMap>::namespaced(client.clone(), "default");
    let mut config_map = config_map_api.get(&config_map_name).await
        .map_err(|e| Error::FaultInjectionError("Fail to get fault injection config"))?;
    println!("Get {}: {}", config_map_name, deps_hack::k8s_openapi::serde_json::to_string(&config_map).unwrap());
    let data = config_map.data.as_ref().ok_or_else(|| Error::FaultInjectionError("Fail to unwrap data"))?;
    let current_val = data.get("current").ok_or_else(|| Error::FaultInjectionError("Fail to get current"))?;
    let current = current_val.parse::<i32>().map_err(|e| Error::FaultInjectionError("Fail to parse current value to i32"))?;
    let expected_val = data.get("expected").ok_or_else(|| Error::FaultInjectionError("Fail to get expected"))?;
    let expected = expected_val.parse::<i32>().map_err(|e| Error::FaultInjectionError("Fail to parse expected value to i32"))?;
    config_map.data.as_mut().unwrap().insert("current".to_string(), (current + 1).to_string());
    config_map_api.replace(config_map_name, &PostParams::default(), &config_map).await
        .map_err(|e| Error::FaultInjectionError("Fail to update fault injection config"))?;

    if current == expected {
        // Now it is time to crash according to fault-injection-config
        panic!();
    }

    return Ok(());
}

}
