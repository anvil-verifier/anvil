// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::container::*;
use crate::kubernetes_api_objects::exec::object_meta::*;
use crate::kubernetes_api_objects::exec::resource::*;
use crate::vstd_ext::string_map::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {
// Tests for life cycle handler
#[test]
#[verifier(external)]
pub fn test_set_exec() {
    let mut handler = LifecycleHandler::default();
    let mut exec_action = ExecAction::default();
    exec_action.set_command(vec![new_strlit("command").to_string()]);
    handler.set_exec(exec_action.clone());
    assert_eq!(exec_action.into_kube(), handler.into_kube().exec.unwrap());
}

#[test]
#[verifier(external)]
pub fn test_default(){
    let handler = LifecycleHandler::default();
    assert_eq!(handler.into_kube(), deps_hack::k8s_openapi::api::core::v1::LifecycleHandler::default());
}

#[test]
#[verifier(external)]
pub fn test_clone(){
    let mut handler = LifecycleHandler::default();
    let mut exec_action = ExecAction::default();
    exec_action.set_command(vec![new_strlit("command").to_string()]);
    handler.set_exec(exec_action.clone());
    let handler_clone = handler.clone();
    assert_eq!(handler.into_kube(), handler_clone.into_kube());
}

#[test]
#[verifier(external)]
pub fn test_kube(){
    let kube_handler = deps_hack::k8s_openapi::api::core::v1::LifecycleHandler {
        exec: Some(deps_hack::k8s_openapi::api::core::v1::ExecAction {
            command: Some(vec!["command".to_string()]),
        }),
        ..Default::default()
    };

    let handler = LifecycleHandler::from_kube(kube_handler.clone());

    assert_eq!(handler.into_kube(), kube_handler);
}

}
