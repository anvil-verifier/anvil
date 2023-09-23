// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::container::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
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
pub fn test_set_exec() {
    let mut handler = LifecycleHandler::default();
    let mut exec_action = ExecAction::default();
    exec_action.set_command(vec![new_strlit("command").to_string()]);
    handler.set_exec(exec_action.clone());
    assert_eq!(exec_action.into_kube(), handler.into_kube().exec.unwrap());
}

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
}
