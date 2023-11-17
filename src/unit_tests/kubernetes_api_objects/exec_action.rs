// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for life cycle
#[test]
#[verifier(external)]
pub fn test_set_command() {
    let mut exec_action = ExecAction::default();
    exec_action.set_command(vec![new_strlit("command").to_string()]);
    assert_eq!(
        vec!["command".to_string()],
        exec_action.into_kube().command.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_default() {
    let exec_action = ExecAction::default();
    assert_eq!(
        exec_action.into_kube(),
        deps_hack::k8s_openapi::api::core::v1::ExecAction::default()
    );
}

#[test]
#[verifier(external)]
pub fn test_clone() {
    let mut exec_action = ExecAction::default();
    exec_action.set_command(vec![new_strlit("command").to_string()]);
    let exec_action_clone = exec_action.clone();
    assert_eq!(exec_action.into_kube(), exec_action_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube() {
    let kube_exec_action = deps_hack::k8s_openapi::api::core::v1::ExecAction {
        command: Some(vec!["command".to_string()]),
    };

    let exec_action = ExecAction::from_kube(kube_exec_action.clone());

    assert_eq!(
        exec_action.into_kube(),
        kube_exec_action
    );
}

}
