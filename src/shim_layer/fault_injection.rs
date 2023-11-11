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
pub async fn crash_or_continue(client: &Client, cr_key: &String, log_header: &String) -> Result<(), String> {
    // We require the fault injection configuration is stored by a ConfigMap object
    // in the default namespace called "fault-injection-config"
    let config_map_name = "fault-injection-config";
    let config_map_api = Api::<ConfigMap>::namespaced(client.clone(), "default");
    let mut config_map = config_map_api.get(&config_map_name).await
        .map_err(|_e| "Fail to get fault injection config".to_string())?;
    println!("{} Get {}: {}", log_header, config_map_name, deps_hack::k8s_openapi::serde_json::to_string(&config_map).unwrap());
    let data = config_map.data.as_ref().ok_or_else(|| "Fail to unwrap data".to_string())?;
    // The configuration should tell us a cr_key and we will crash the controller when it is managing that object
    // This is to make the fault injection more deterministic when the controller manages multiple cr objects of different types
    let cr_key_val = data.get("cr_key").ok_or_else(|| "Fail to get cr_key".to_string())?;
    // We only want to crash when the controller is managing the object identified by cr_key
    if cr_key_val.to_string() != cr_key.to_string() {
        return Ok(());
    }
    // The configuration should have the two entries:
    // 1. the current number of requests that the controller has issued, and
    // 2. the expected number of requests after which the controller should crash
    let current_val = data.get("current").ok_or_else(|| "Fail to get current".to_string())?;
    let current = current_val.parse::<i32>().map_err(|_e| "Fail to parse current value to i32".to_string())?;
    let expected_val = data.get("expected").ok_or_else(|| "Fail to get expected".to_string())?;
    let expected = expected_val.parse::<i32>().map_err(|_e| "Fail to parse expected value to i32".to_string())?;
    // We increment current entry here before panic, otherwise we might end up crashing at the same point forever
    config_map.data.as_mut().unwrap().insert("current".to_string(), (current + 1).to_string());
    config_map_api.replace(config_map_name, &PostParams::default(), &config_map).await
        .map_err(|_e| "Fail to update fault injection config".to_string())?;
    if current == expected {
        // Now it is time to crash according to fault-injection-config
        panic!();
    }
    return Ok(());
}

}
