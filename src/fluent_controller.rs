// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#![allow(unused_imports)]

#[path = "controller_examples/fluent_controller/mod.rs"]
pub mod fluent_controller;
pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod pervasive_ext;
pub mod reconciler;
pub mod external_api;
pub mod shim_layer;
pub mod state_machine;
pub mod temporal_logic;

// TODO(xudong): implement verified fluent-controller
fn main() {}
