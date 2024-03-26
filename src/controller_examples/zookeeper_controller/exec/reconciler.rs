// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::{
    api_method::*, container::*, label_selector::*, object_meta::*, owner_reference::*,
    persistent_volume_claim::*, pod::*, pod_template_spec::*, prelude::*, resource::*,
    resource_requirements::*, volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::reconciler::spec::resource_builder::ResourceBuilder as SpecResourceBuilder;
use crate::vstd_ext::{string_map::*, string_view::*};
use crate::zookeeper_controller::exec::resource::*;
use crate::zookeeper_controller::model::reconciler as model_reconciler;
use crate::zookeeper_controller::model::resource as model_resource;
use crate::zookeeper_controller::trusted::{
    exec_types::*, spec_types, step::*, zookeeper_api_exec::*, zookeeper_api_spec::*,
};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;
use vstd::view::*;

verus! {

pub struct ZookeeperReconciler {}

impl Reconciler for ZookeeperReconciler {
    type R = ZookeeperCluster;
    type T = ZookeeperReconcileState;
    type ExternalAPIType = ZKAPIShimLayer;

    open spec fn well_formed(zk: &ZookeeperCluster) -> bool { zk@.well_formed() }

    fn reconcile_init_state() -> ZookeeperReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(zk: &ZookeeperCluster, resp_o: Option<Response<ZKAPIOutput>>, state: ZookeeperReconcileState)
    -> (ZookeeperReconcileState, Option<Request<ZKAPIInput>>) {
        reconcile_core(zk, resp_o, state)
    }

    fn reconcile_done(state: &ZookeeperReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(state: &ZookeeperReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for ZookeeperReconciler {
    fn default() -> ZookeeperReconciler { ZookeeperReconciler{} }
}

pub fn reconcile_init_state() -> (state: ZookeeperReconcileState)
    ensures state@ == model_reconciler::reconcile_init_state(),
{
    ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Init,
        latest_config_map_rv_opt: None,
    }
}

pub fn reconcile_done(state: &ZookeeperReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_done(state@),
{
    match state.reconcile_step {
        ZookeeperReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &ZookeeperReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_error(state@),
{
    match state.reconcile_step {
        ZookeeperReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(
    zk: &ZookeeperCluster, resp_o: Option<Response<ZKAPIOutput>>, state: ZookeeperReconcileState
) -> (res: (ZookeeperReconcileState, Option<Request<ZKAPIInput>>))
    requires zk@.well_formed(),
    ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_core(zk@, opt_response_to_view(&resp_o), state@),
        // resource_version_check(opt_response_to_view(&resp_o), opt_request_to_view(&res.1)),
{
    let step = state.reconcile_step;
    match step {
        ZookeeperReconcileStep::Init => {
            let req_o = KubeAPIRequest::GetRequest(HeadlessServiceBuilder::get_request(zk));
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::HeadlessService),
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        ZookeeperReconcileStep::AfterKRequestStep(_, resource) => {
            match resource {
                SubResource::HeadlessService => reconcile_helper::<model_resource::HeadlessServiceBuilder, HeadlessServiceBuilder>(zk, resp_o, state),
                SubResource::ClientService => reconcile_helper::<model_resource::ClientServiceBuilder, ClientServiceBuilder>(zk, resp_o, state),
                SubResource::AdminServerService => reconcile_helper::<model_resource::AdminServerServiceBuilder, AdminServerServiceBuilder>(zk, resp_o, state),
                SubResource::ConfigMap => reconcile_helper::<model_resource::ConfigMapBuilder, ConfigMapBuilder>(zk, resp_o, state),
                SubResource::StatefulSet => reconcile_helper::<model_resource::StatefulSetBuilder, StatefulSetBuilder>(zk, resp_o, state),
            }
        },
        ZookeeperReconcileStep::AfterExistsStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_stateful_set_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_stateful_set_resp.is_ok() {
                    // Updating the stateful set can lead to downscale,
                    // which also requires to remove the zookeeper replica from the membership list explicitly.
                    // If the zookeeper replica is deleted without being removed from the membership,
                    // the zookeeper cluster might be unavailable because of losing the quorum.
                    // So the controller needs to correctly prompt membership change before reducing the replica
                    // size of the stateful set, by writing the new replica size into the zookeeper API.
                    // Details can be found in https://github.com/vmware-research/verifiable-controllers/issues/174.
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterExistsZKNode,
                        ..state
                    };
                    let node_path = zk_node_path(zk);
                    let ext_req = ZKAPIInput::ExistsRequest(
                        zk.metadata().name().unwrap(), zk.metadata().namespace().unwrap(), zk.spec().ports().client(), node_path
                    );
                    return (state_prime, Some(Request::ExternalRequest(ext_req)));
                } else if get_stateful_set_resp.unwrap_err().is_object_not_found() {
                    let req_o = KubeAPIRequest::GetRequest(StatefulSetBuilder::get_request(zk));
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::StatefulSet),
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterExistsZKNode => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_external_response()
            && resp_o.as_ref().unwrap().as_external_response_ref().is_exists_response() {
                let exists_resp = resp_o.unwrap().into_external_response().unwrap_exists_response().res;
                if exists_resp.is_ok() {
                    let version_o = exists_resp.unwrap();
                    if version_o.is_some() {
                        let version = version_o.unwrap();
                        let node_path = zk_node_path(zk);
                        let data = zk_node_data(zk);
                        let ext_req = ZKAPIInput::SetDataRequest(
                            zk.metadata().name().unwrap(), zk.metadata().namespace().unwrap(), zk.spec().ports().client(), node_path, data, version
                        );
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterUpdateZKNode,
                            ..state
                        };
                        return (state_prime, Some(Request::ExternalRequest(ext_req)));
                    } else {
                        let node_path = zk_parent_node_path(zk);
                        let data = new_strlit("").to_string();
                        let ext_req = ZKAPIInput::CreateRequest(
                            zk.metadata().name().unwrap(), zk.metadata().namespace().unwrap(), zk.spec().ports().client(), node_path, data
                        );
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterCreateZKParentNode,
                            ..state
                        };
                        return (state_prime, Some(Request::ExternalRequest(ext_req)));
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterCreateZKParentNode => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_external_response()
            && resp_o.as_ref().unwrap().as_external_response_ref().is_create_response() {
                let create_resp = resp_o.unwrap().into_external_response().unwrap_create_response().res;
                if create_resp.is_ok() || create_resp.unwrap_err().is_create_already_exists() {
                    let node_path = zk_node_path(zk);
                    let data = zk_node_data(zk);
                    let ext_req = ZKAPIInput::CreateRequest(
                        zk.metadata().name().unwrap(), zk.metadata().namespace().unwrap(), zk.spec().ports().client(), node_path, data
                    );
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateZKNode,
                        ..state
                    };
                    return (state_prime, Some(Request::ExternalRequest(ext_req)));
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterCreateZKNode => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_external_response()
            && resp_o.as_ref().unwrap().as_external_response_ref().is_create_response()
            && resp_o.unwrap().into_external_response().unwrap_create_response().res.is_ok() {
                let req_o = KubeAPIRequest::GetRequest(StatefulSetBuilder::get_request(zk));
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::StatefulSet),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterUpdateZKNode => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_external_response()
            && resp_o.as_ref().unwrap().as_external_response_ref().is_set_data_response()
            && resp_o.unwrap().into_external_response().unwrap_set_data_response().res.is_ok() {
                let req_o = KubeAPIRequest::GetRequest(StatefulSetBuilder::get_request(zk));
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::StatefulSet),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterUpdateStatus => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_status_response() {
                let update_status_resp = resp_o.unwrap().into_k_response().into_update_status_response().res;
                if update_status_resp.is_ok() {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Done,
                        ..state
                    };
                    return (state_prime, None);
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        _ => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: step,
                ..state
            };
            return (state_prime, None);
        }
    }
}

pub fn reconcile_helper<
    SpecBuilder: SpecResourceBuilder<spec_types::ZookeeperClusterView, spec_types::ZookeeperReconcileState>,
    Builder: ResourceBuilder<ZookeeperCluster, ZookeeperReconcileState, SpecBuilder>
>(
    zk: &ZookeeperCluster, resp_o: Option<Response<ZKAPIOutput>>, state: ZookeeperReconcileState
) -> (res: (ZookeeperReconcileState, Option<Request<ZKAPIInput>>))
    requires
        zk@.well_formed(),
        Builder::requirements(zk@),
        state.reconcile_step.is_AfterKRequestStep(),
    ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_helper::<SpecBuilder>(zk@, opt_response_to_view(&resp_o), state@),
{
    let step = state.reconcile_step.clone();
    match step {
        ZookeeperReconcileStep::AfterKRequestStep(action, resource) => {
            match action {
                ActionKind::Get => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                        let get_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                        if get_resp.is_ok() {
                            let new_obj = Builder::update(zk, &state, get_resp.unwrap());
                            if new_obj.is_ok() {
                                let updated_obj = new_obj.unwrap();
                                let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                                    api_resource: Builder::get_request(zk).api_resource,
                                    name: Builder::get_request(zk).name,
                                    namespace: zk.metadata().namespace().unwrap(),
                                    obj: updated_obj,
                                });
                                let state_prime = ZookeeperReconcileState {
                                    reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Update, resource),
                                    ..state
                                };
                                return (state_prime, Some(Request::KRequest(req_o)));
                            }
                        } else if get_resp.unwrap_err().is_object_not_found() {
                            // create
                            let new_obj = Builder::make(zk, &state);
                            if new_obj.is_ok() {
                                let created_obj = new_obj.unwrap();
                                let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                                    api_resource: Builder::get_request(zk).api_resource,
                                    namespace: zk.metadata().namespace().unwrap(),
                                    obj: created_obj,
                                });
                                let state_prime = ZookeeperReconcileState {
                                    reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Create, resource),
                                    ..state
                                };
                                return (state_prime, Some(Request::KRequest(req_o)));
                            }
                        }
                    }
                    // return error state
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
                },
                ActionKind::Create => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok() {
                        let next_state = Builder::state_after_create(zk, resp_o.unwrap().into_k_response().into_create_response().res.unwrap(), state.clone());
                        if next_state.is_ok() {
                            let (state_prime, req) = next_state.unwrap();
                            let req_o = if req.is_some() {
                                Some(Request::KRequest(req.unwrap()))
                            } else {
                                None
                            };
                            return (state_prime, req_o);
                        }
                    }
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
                },
                ActionKind::Update => {
                    if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
                    && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok() {
                        let next_state = Builder::state_after_update(zk, resp_o.unwrap().into_k_response().into_update_response().res.unwrap(), state.clone());
                        if next_state.is_ok() {
                            let (state_prime, req) = next_state.unwrap();
                            let req_o = if req.is_some() {
                                Some(Request::KRequest(req.unwrap()))
                            } else {
                                None
                            };
                            return (state_prime, req_o);
                        }
                    }
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    let req_o = None;
                    return (state_prime, req_o);
                },
            }
        },
        _ => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
    }
}

fn zk_node_path(zk: &ZookeeperCluster) -> (path: Vec<String>)
    requires zk@.well_formed(),
    ensures path@.map_values(|s: String| s@) == model_reconciler::zk_node_path(zk@),
{
    let mut path = Vec::new();
    path.push(new_strlit("zookeeper-operator").to_string());
    path.push(zk.metadata().name().unwrap());
    proof { assert_seqs_equal!(path@.map_values(|s: String| s@), model_reconciler::zk_node_path(zk@)); }
    path
}

fn zk_parent_node_path(zk: &ZookeeperCluster) -> (path: Vec<String>)
    requires zk@.well_formed(),
    ensures path@.map_values(|s: String| s@) == model_reconciler::zk_parent_node_path(zk@),
{
    let mut path = Vec::new();
    path.push(new_strlit("zookeeper-operator").to_string());
    proof { assert_seqs_equal!(path@.map_values(|s: String| s@), model_reconciler::zk_parent_node_path(zk@)); }
    path
}

fn zk_node_data(zk: &ZookeeperCluster) -> (data: String)
    requires zk@.well_formed(),
    ensures data@ == model_reconciler::zk_node_data(zk@),
{
    new_strlit("CLUSTER_SIZE=").to_string().concat(i32_to_string(zk.spec().replicas()).as_str())
}

impl ZKAPIOutput {
    pub fn is_exists_response(&self) -> (res: bool)
        ensures res == self.is_ExistsResponse(),
    {
        match self {
            ZKAPIOutput::ExistsResponse(_) => true,
            _ => false,
        }
    }

    pub fn unwrap_exists_response(self) -> (result: ZKAPIExistsResult)
        requires self.is_ExistsResponse(),
        ensures result == self.get_ExistsResponse_0(),
    {
        match self {
            ZKAPIOutput::ExistsResponse(result) => result,
            _ => unreached(),
        }
    }

    pub fn is_create_response(&self) -> (res: bool)
        ensures res == self.is_CreateResponse(),
    {
        match self {
            ZKAPIOutput::CreateResponse(_) => true,
            _ => false,
        }
    }

    pub fn unwrap_create_response(self) -> (result: ZKAPICreateResult)
        requires self.is_CreateResponse(),
        ensures result == self.get_CreateResponse_0(),
    {
        match self {
            ZKAPIOutput::CreateResponse(result) => result,
            _ => unreached(),
        }
    }

    pub fn is_set_data_response(&self) -> (res: bool)
        ensures res == self.is_SetDataResponse(),
    {
        match self {
            ZKAPIOutput::SetDataResponse(_) => true,
            _ => false,
        }
    }

    pub fn unwrap_set_data_response(self) -> (result: ZKAPISetDataResult)
        requires self.is_SetDataResponse(),
        ensures result == self.get_SetDataResponse_0(),
    {
        match self {
            ZKAPIOutput::SetDataResponse(result) => result,
            _ => unreached(),
        }
    }
}


}
