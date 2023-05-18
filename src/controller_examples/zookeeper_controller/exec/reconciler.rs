// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_examples::zookeeper_controller::spec::zookeepercluster::*;
use crate::kubernetes_api_objects::{api_method::*, common::*, config_map::*, service::*};
use crate::pervasive_ext::string_map::StringMap;
use crate::reconciler::exec::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::string::*;
use vstd::vec::*;

verus! {

/// ZookeeperReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct ZookeeperReconcileState {
    // reconcile_step, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_step: ZookeeperReconcileStep,
}

#[is_variant]
pub enum ZookeeperReconcileStep {
    Init,
    AfterGetCR,
    Done,
    Error,
}

impl ZookeeperReconcileStep {

    pub fn clone(&self) -> (res: ZookeeperReconcileStep)
        ensures res == self
    {
        match self {
            ZookeeperReconcileStep::Init => ZookeeperReconcileStep::Init,
            ZookeeperReconcileStep::AfterGetCR => ZookeeperReconcileStep::AfterGetCR,
            ZookeeperReconcileStep::Done => ZookeeperReconcileStep::Done,
            ZookeeperReconcileStep::Error => ZookeeperReconcileStep::Error,
        }
    }

    #[inline(always)]
    pub const fn is_init(&self) -> (res: bool)
        ensures res <==> self.is_Init(),
    {
        match self {
            ZookeeperReconcileStep::Init => true,
            _ => false,
        }
    }

    #[inline(always)]
    pub const fn is_after_get_cr(&self) -> (res: bool)
        ensures res <==> self.is_AfterGetCR(),
    {
        match self {
            ZookeeperReconcileStep::AfterGetCR => true,
            _ => false,
        }
    }

    #[inline(always)]
    pub const fn is_done(&self) -> (res: bool)
        ensures res <==> self.is_Done(),
    {
        match self {
            ZookeeperReconcileStep::Done => true,
            _ => false,
        }
    }

    #[inline(always)]
    pub const fn is_error(&self) -> (res: bool)
        ensures res <==> self.is_Error(),
    {
        match self {
            ZookeeperReconcileStep::Error => true,
            _ => false,
        }
    }
}

pub struct ZookeeperReconciler {}

#[verifier(external)]
impl Reconciler<ZookeeperReconcileState> for ZookeeperReconciler {
    fn reconcile_init_state(&self) -> ZookeeperReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, cr_key: &KubeObjectRef, resp_o: &Option<KubeAPIResponse>, state: &ZookeeperReconcileState) -> (ZookeeperReconcileState, Option<KubeAPIRequest>) {
        reconcile_core(cr_key, resp_o, state)
    }

    fn reconcile_done(&self, state: &ZookeeperReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(&self, state: &ZookeeperReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for ZookeeperReconciler {
    fn default() -> ZookeeperReconciler { ZookeeperReconciler{} }
}

pub fn reconcile_init_state() -> ZookeeperReconcileState {
    ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Init,
    }
}

pub fn reconcile_done(state: &ZookeeperReconcileState) -> (res: bool) {
    state.reconcile_step.is_done()
}

pub fn reconcile_error(state: &ZookeeperReconcileState) -> (res: bool) {
    state.reconcile_step.is_error()
}

pub fn reconcile_core(cr_key: &KubeObjectRef, resp_o: &Option<KubeAPIResponse>, state: &ZookeeperReconcileState) -> (res: (ZookeeperReconcileState, Option<KubeAPIRequest>)) {
    let step = &state.reconcile_step;
    match step {
        ZookeeperReconcileStep::Init => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterGetCR,
            };
            let req_o = Option::Some(KubeAPIRequest::GetRequest(
                KubeGetRequest {
                    api_resource: ZookeeperCluster::api_resource(),
                    name: cr_key.name.clone(),
                    namespace: cr_key.namespace.clone(),
                }
            ));
            (state_prime, req_o)
        },
        ZookeeperReconcileStep::AfterGetCR => {
            if resp_o.is_some() {
                let resp = resp_o.as_ref().unwrap();
                if resp.is_get_response() && resp.as_get_response_ref().res.is_ok() {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Done,
                    };
                    let req_o = Option::None;
                    (state_prime, req_o)
                } else {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                    };
                    let req_o = Option::None;
                    (state_prime, req_o)
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                };
                let req_o = Option::None;
                (state_prime, req_o)
            }
        },
        _ => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: step.clone(),
            };
            let req_o = Option::None;
            (state_prime, req_o)
        }
    }
}

fn make_service(zk: &ZookeeperCluster, name: String, ports: Vec<ServicePort>, cluster_ip: bool) -> Service
    requires
        zk@.metadata.name.is_Some(),
        zk@.metadata.namespace.is_Some(),
{
    let mut service = Service::default();
    service.set_name(name);
    service.set_namespace(zk.namespace().unwrap());

    let mut service_spec = ServiceSpec::default();
    if cluster_ip {
        service_spec.set_cluster_ip(new_strlit("None").to_string());
    }
    service_spec.set_ports(ports);

    let mut selector = StringMap::empty();
    selector.insert(new_strlit("app").to_string(), zk.name().unwrap());
    service_spec.set_selector(selector);

    service.set_spec(service_spec);

    service
}

}
