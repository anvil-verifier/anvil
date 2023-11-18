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
pub fn test_set_pre_stop() {
    let mut lifecycle = Lifecycle::default();
    let mut handler = LifecycleHandler::default();
    let mut exec_action = ExecAction::default();
    exec_action.set_command(vec![new_strlit("command").to_string()]);
    handler.set_exec(exec_action);

    lifecycle.set_pre_stop(handler.clone());
    assert_eq!(
        handler.into_kube(),
        lifecycle.into_kube().pre_stop.unwrap()
    );
}

#[test]
#[verifier(external)]
pub fn test_default(){
    let lifecycle = Lifecycle::default();
    assert_eq!(lifecycle.into_kube(), deps_hack::k8s_openapi::api::core::v1::Lifecycle::default());
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
    let kube_lifecycle = deps_hack::k8s_openapi::api::core::v1::Lifecycle {
        pre_stop: Some(deps_hack::k8s_openapi::api::core::v1::LifecycleHandler {
            exec: Some(deps_hack::k8s_openapi::api::core::v1::ExecAction {
                command: Some(vec!["command".to_string()]),
            }),
            ..Default::default()
        }),
        ..Default::default()
    };

    let lifecycle = Lifecycle::from_kube(kube_lifecycle.clone());

    assert_eq!(lifecycle.into_kube(), kube_lifecycle);
}

}
