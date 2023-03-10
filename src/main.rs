// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

pub mod kubernetes_api_objects;
pub mod kubernetes_cluster;
pub mod pervasive;
pub mod pervasive_ext;
// pub mod simple_controller;
pub mod state_machine;
pub mod temporal_logic;
pub mod tla_examples;

#[verifier(external_body)]
fn main() {}
