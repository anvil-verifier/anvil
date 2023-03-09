// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

pub mod kubernetes_cluster;
pub mod pervasive;
pub mod pervasive_lemmas;
// pub mod simple_controller;
pub mod state_machine;
pub mod temporal_logic;
pub mod tla_examples;

pub mod resources;

#[verifier(external_body)]
fn main() {
}
