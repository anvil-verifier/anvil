// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, container::*, error::*, label_selector::*,
    object_meta::*, owner_reference::*, persistent_volume_claim::*, pod::*, pod_template_spec::*,
    resource::*, resource_requirements::*, service::*, stateful_set::*, volume::*,
};
use crate::pervasive_ext::{string_map::*, string_view::*, to_view::*};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::exec::{types::*, zookeeper_api::*};
use crate::zookeeper_controller::spec::reconciler as zk_spec;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;
use vstd::view::*;

verus! {

/// ZookeeperReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct ZookeeperReconcileState {
    // reconcile_step, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_step: ZookeeperReconcileStep,
    pub found_stateful_set_opt: Option<StatefulSet>,
    pub latest_config_map_rv_opt: Option<String>,
}

impl ZookeeperReconcileState {
    pub open spec fn to_view(&self) -> zk_spec::ZookeeperReconcileState {
        zk_spec::ZookeeperReconcileState {
            reconcile_step: self.reconcile_step,
            found_stateful_set_opt: match &self.found_stateful_set_opt {
                Some(sts) => Some(sts@),
                None => None,
            },
            latest_config_map_rv_opt: match &self.latest_config_map_rv_opt {
                Some(s) => Some(s@),
                None => None,
            },
        }
    }
}

pub struct ZookeeperReconciler {}

#[verifier(external)]
impl Reconciler<ZookeeperCluster, ZookeeperReconcileState, ZKAPIInput, ZKAPIOutput, ZKAPIShimLayer> for ZookeeperReconciler {
    fn reconcile_init_state(&self) -> ZookeeperReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(
        &self, zk: &ZookeeperCluster, resp_o: Option<Response<ZKAPIOutput>>, state: ZookeeperReconcileState
    ) -> (ZookeeperReconcileState, Option<Request<ZKAPIInput>>) {
        reconcile_core(zk, resp_o, state)
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

pub fn reconcile_init_state() -> (state: ZookeeperReconcileState)
    ensures
        state.to_view() == zk_spec::reconcile_init_state(),
{
    ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Init,
        found_stateful_set_opt: None,
        latest_config_map_rv_opt: None,
    }
}

pub fn reconcile_done(state: &ZookeeperReconcileState) -> (res: bool)
    ensures
        res == zk_spec::reconcile_done(state.to_view()),
{
    match state.reconcile_step {
        ZookeeperReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &ZookeeperReconcileState) -> (res: bool)
    ensures
        res == zk_spec::reconcile_error(state.to_view()),
{
    match state.reconcile_step {
        ZookeeperReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(
    zk: &ZookeeperCluster, resp_o: Option<Response<ZKAPIOutput>>, state: ZookeeperReconcileState
) -> (res: (ZookeeperReconcileState, Option<Request<ZKAPIInput>>))
    requires
        zk@.well_formed(),
    ensures
        (res.0.to_view(), opt_request_to_view(&res.1)) == zk_spec::reconcile_core(zk@, opt_response_to_view(&resp_o), state.to_view()),
{
    let step = state.reconcile_step;
    match step {
        ZookeeperReconcileStep::Init => {
            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: Service::api_resource(),
                name: make_headless_service_name(zk),
                namespace: zk.metadata().namespace().unwrap(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterGetHeadlessService,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        ZookeeperReconcileStep::AfterGetHeadlessService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_headless_service_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_headless_service_resp.is_ok() {
                    let unmarshal_headless_service_result = Service::unmarshal(get_headless_service_resp.unwrap());
                    if unmarshal_headless_service_result.is_ok() {
                        // Update the headless service with the new port.
                        let found_headless_service = unmarshal_headless_service_result.unwrap();
                        if found_headless_service.spec().is_some() {
                            let new_headless_service = update_headless_service(zk, &found_headless_service);
                            let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                                api_resource: Service::api_resource(),
                                name: make_headless_service_name(zk),
                                namespace: zk.metadata().namespace().unwrap(),
                                obj: new_headless_service.marshal(),
                            });
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::AfterUpdateHeadlessService,
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req_o)));
                        }
                    }
                } else if get_headless_service_resp.unwrap_err().is_object_not_found() {
                    // Create the headless service since it doesn't exist yet.
                    let headless_service = make_headless_service(zk);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Service::api_resource(),
                        namespace: zk.metadata().namespace().unwrap(),
                        obj: headless_service.marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateHeadlessService,
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
        ZookeeperReconcileStep::AfterCreateHeadlessService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response() {
                let create_headless_service_resp = resp_o.unwrap().into_k_response().into_create_response().res;
                if create_headless_service_resp.is_ok() {
                    let unmarshal_headless_service_result = Service::unmarshal(create_headless_service_resp.unwrap());
                    if unmarshal_headless_service_result.is_ok() {
                        let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                            api_resource: Service::api_resource(),
                            name: make_client_service_name(zk),
                            namespace: zk.metadata().namespace().unwrap(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterGetClientService,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterUpdateHeadlessService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response() {
                let update_headless_service_resp = resp_o.unwrap().into_k_response().into_update_response().res;
                if update_headless_service_resp.is_ok() {
                    let unmarshal_headless_service_result = Service::unmarshal(update_headless_service_resp.unwrap());
                    if unmarshal_headless_service_result.is_ok() {
                        let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                            api_resource: Service::api_resource(),
                            name: make_client_service_name(zk),
                            namespace: zk.metadata().namespace().unwrap(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterGetClientService,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterGetClientService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_client_service_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_client_service_resp.is_ok() {
                    let unmarshal_client_service_result = Service::unmarshal(get_client_service_resp.unwrap());
                    if unmarshal_client_service_result.is_ok() {
                        // Update the client service with the new port.
                        let found_client_service = unmarshal_client_service_result.unwrap();
                        if found_client_service.spec().is_some() {
                            let new_client_service = update_client_service(zk, &found_client_service);
                            let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                                api_resource: Service::api_resource(),
                                name: make_client_service_name(zk),
                                namespace: zk.metadata().namespace().unwrap(),
                                obj: new_client_service.marshal(),
                            });
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::AfterUpdateClientService,
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req_o)));
                        }
                    }
                } else if get_client_service_resp.unwrap_err().is_object_not_found() {
                    // Create the client service since it doesn't exist yet.
                    let client_service = make_client_service(zk);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Service::api_resource(),
                        namespace: zk.metadata().namespace().unwrap(),
                        obj: client_service.marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateClientService,
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
        ZookeeperReconcileStep::AfterCreateClientService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response() {
                let create_client_service_resp = resp_o.unwrap().into_k_response().into_create_response().res;
                if create_client_service_resp.is_ok() {
                    let unmarshal_client_service_result = Service::unmarshal(create_client_service_resp.unwrap());
                    if unmarshal_client_service_result.is_ok() {
                        let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                            api_resource: Service::api_resource(),
                            name: make_admin_server_service_name(zk),
                            namespace: zk.metadata().namespace().unwrap(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterGetAdminServerService,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterUpdateClientService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response() {
                let update_client_service_resp = resp_o.unwrap().into_k_response().into_update_response().res;
                if update_client_service_resp.is_ok() {
                    let unmarshal_client_service_result = Service::unmarshal(update_client_service_resp.unwrap());
                    if unmarshal_client_service_result.is_ok() {
                        let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                            api_resource: Service::api_resource(),
                            name: make_admin_server_service_name(zk),
                            namespace: zk.metadata().namespace().unwrap(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterGetAdminServerService,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterGetAdminServerService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_admin_server_service_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_admin_server_service_resp.is_ok() {
                    let unmarshal_admin_server_service_result = Service::unmarshal(get_admin_server_service_resp.unwrap());
                    if unmarshal_admin_server_service_result.is_ok() {
                        // Update the admin_server service with the new port.
                        let found_admin_server_service = unmarshal_admin_server_service_result.unwrap();
                        if found_admin_server_service.spec().is_some() {
                            let new_admin_server_service = update_admin_server_service(zk, &found_admin_server_service);
                            let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                                api_resource: Service::api_resource(),
                                name: make_admin_server_service_name(zk),
                                namespace: zk.metadata().namespace().unwrap(),
                                obj: new_admin_server_service.marshal(),
                            });
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::AfterUpdateAdminServerService,
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req_o)));
                        }
                    }
                } else if get_admin_server_service_resp.unwrap_err().is_object_not_found() {
                    // Create the admin_server service since it doesn't exist yet.
                    let admin_server_service = make_admin_server_service(zk);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Service::api_resource(),
                        namespace: zk.metadata().namespace().unwrap(),
                        obj: admin_server_service.marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateAdminServerService,
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
        ZookeeperReconcileStep::AfterCreateAdminServerService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response() {
                let create_admin_server_service_resp = resp_o.unwrap().into_k_response().into_create_response().res;
                if create_admin_server_service_resp.is_ok() {
                    let unmarshal_admin_server_service_result = Service::unmarshal(create_admin_server_service_resp.unwrap());
                    if unmarshal_admin_server_service_result.is_ok() {
                        let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                            api_resource: ConfigMap::api_resource(),
                            name: make_config_map_name(zk),
                            namespace: zk.metadata().namespace().unwrap(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterGetConfigMap,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterUpdateAdminServerService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response() {
                let update_admin_server_service_resp = resp_o.unwrap().into_k_response().into_update_response().res;
                if update_admin_server_service_resp.is_ok() {
                    let unmarshal_admin_server_service_result = Service::unmarshal(update_admin_server_service_resp.unwrap());
                    if unmarshal_admin_server_service_result.is_ok() {
                        let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                            api_resource: ConfigMap::api_resource(),
                            name: make_config_map_name(zk),
                            namespace: zk.metadata().namespace().unwrap(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterGetConfigMap,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterGetConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_config_map_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_config_map_resp.is_ok() {
                    let unmarshal_config_map_result = ConfigMap::unmarshal(get_config_map_resp.unwrap());
                    if unmarshal_config_map_result.is_ok() {
                        // Update the config map with the new configuration data
                        let found_config_map = unmarshal_config_map_result.unwrap();
                        let new_config_map = update_config_map(zk, &found_config_map);
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: ConfigMap::api_resource(),
                            name: make_config_map_name(zk),
                            namespace: zk.metadata().namespace().unwrap(),
                            obj: new_config_map.marshal(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterUpdateConfigMap,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_config_map_resp.unwrap_err().is_object_not_found() {
                    // Create the config map since it doesn't exist yet.
                    let config_map = make_config_map(zk);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: ConfigMap::api_resource(),
                        namespace: zk.metadata().namespace().unwrap(),
                        obj: config_map.marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateConfigMap,
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
        ZookeeperReconcileStep::AfterCreateConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response() {
                let create_config_map_resp = resp_o.unwrap().into_k_response().into_create_response().res;
                if create_config_map_resp.is_ok() {
                    let unmarshal_config_map_result = ConfigMap::unmarshal(create_config_map_resp.unwrap());
                    if unmarshal_config_map_result.is_ok() {
                        let latest_config_map = unmarshal_config_map_result.unwrap();
                        if latest_config_map.metadata().resource_version().is_some() {
                            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                                api_resource: StatefulSet::api_resource(),
                                name: make_stateful_set_name(zk),
                                namespace: zk.metadata().namespace().unwrap(),
                            });
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet,
                                latest_config_map_rv_opt: latest_config_map.metadata().resource_version(),
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req_o)));
                        }
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterUpdateConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response() {
                let update_config_map_resp = resp_o.unwrap().into_k_response().into_update_response().res;
                if update_config_map_resp.is_ok() {
                    let unmarshal_config_map_result = ConfigMap::unmarshal(update_config_map_resp.unwrap());
                    if unmarshal_config_map_result.is_ok() {
                        let latest_config_map = unmarshal_config_map_result.unwrap();
                        if latest_config_map.metadata().resource_version().is_some() {
                            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                                api_resource: StatefulSet::api_resource(),
                                name: make_stateful_set_name(zk),
                                namespace: zk.metadata().namespace().unwrap(),
                            });
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet,
                                latest_config_map_rv_opt: latest_config_map.metadata().resource_version(),
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req_o)));
                        }
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterGetStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_stateful_set_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_stateful_set_resp.is_ok() {
                    let unmarshal_stateful_set_result = StatefulSet::unmarshal(get_stateful_set_resp.unwrap());
                    if unmarshal_stateful_set_result.is_ok() {
                        let found_stateful_set = unmarshal_stateful_set_result.unwrap();
                        // Only proceed if the stateful set is owned by the current cr
                        // so that we won't accidentally update ports or some other mutable fields.
                        if found_stateful_set.metadata().owner_references_only_contains(zk.controller_owner_ref()) {
                            // Updating the stateful set can lead to downscale,
                            // which also requires to remove the zookeeper replica from the membership list explicitly.
                            // If the zookeeper replica is deleted without being removed from the membership,
                            // the zookeeper cluster might be unavailable because of losing the quorum.
                            // So the controller needs to correctly prompt membership change before reducing the replica
                            // size of the stateful set, by writing the new replica size into the zookeeper API.
                            // Details can be found in https://github.com/vmware-research/verifiable-controllers/issues/174.
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::AfterExistsZKNode,
                                // Save the stateful set found by the get request.
                                // Later when we want to update sts, we can use the old sts as the base
                                // and we do not need to call GetRequest again.
                                found_stateful_set_opt: Some(found_stateful_set),
                                ..state
                            };
                            let node_path = zk_node_path(zk);
                            let ext_req = ZKAPIInput::ExistsRequest(
                                zk.metadata().name().unwrap(), zk.metadata().namespace().unwrap(), zk.spec().ports().client(), node_path
                            );
                            return (state_prime, Some(Request::ExternalRequest(ext_req)));
                        }
                    }
                } else if get_stateful_set_resp.unwrap_err().is_object_not_found() && state.latest_config_map_rv_opt.is_some() {
                    // Create the stateful set since it doesn't exist yet.
                    let stateful_set = make_stateful_set(zk, state.latest_config_map_rv_opt.as_ref().unwrap());
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: StatefulSet::api_resource(),
                        namespace: zk.metadata().namespace().unwrap(),
                        obj: stateful_set.marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateStatefulSet,
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
            && resp_o.unwrap().into_external_response().unwrap_create_response().res.is_ok()
            && state.found_stateful_set_opt.is_some() && state.latest_config_map_rv_opt.is_some() {
                // Update the stateful set only after we ensure
                // that the ZK node has been set correctly.
                let found_stateful_set = state.found_stateful_set_opt.as_ref().unwrap();
                if found_stateful_set.spec().is_some() {
                    let latest_config_map_rv = state.latest_config_map_rv_opt.as_ref().unwrap();
                    let new_stateful_set = update_stateful_set(zk, found_stateful_set, latest_config_map_rv);
                    let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                        api_resource: StatefulSet::api_resource(),
                        name: make_stateful_set_name(zk),
                        namespace: zk.metadata().namespace().unwrap(),
                        obj: new_stateful_set.marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterUpdateStatefulSet,
                        found_stateful_set_opt: None,
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
        ZookeeperReconcileStep::AfterUpdateZKNode => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_external_response()
            && resp_o.as_ref().unwrap().as_external_response_ref().is_set_data_response()
            && resp_o.unwrap().into_external_response().unwrap_set_data_response().res.is_ok()
            && state.found_stateful_set_opt.is_some() && state.latest_config_map_rv_opt.is_some() {
                // Update the stateful set only after we ensure
                // that the ZK node has been set correctly.
                let found_stateful_set = state.found_stateful_set_opt.as_ref().unwrap();
                if found_stateful_set.spec().is_some() {
                    let latest_config_map_rv = state.latest_config_map_rv_opt.as_ref().unwrap();
                    let new_stateful_set = update_stateful_set(zk, found_stateful_set, latest_config_map_rv);
                    let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                        api_resource: StatefulSet::api_resource(),
                        name: make_stateful_set_name(zk),
                        namespace: zk.metadata().namespace().unwrap(),
                        obj: new_stateful_set.marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterUpdateStatefulSet,
                        found_stateful_set_opt: None,
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
        ZookeeperReconcileStep::AfterCreateStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response() {
                let create_stateful_set_resp = resp_o.unwrap().into_k_response().into_create_response().res;
                if create_stateful_set_resp.is_ok() {
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
        ZookeeperReconcileStep::AfterUpdateStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response() {
                let update_stateful_set_resp = resp_o.unwrap().into_k_response().into_update_response().res;
                if update_stateful_set_resp.is_ok() {
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

fn zk_node_path(zk: &ZookeeperCluster) -> (path: Vec<String>)
    requires
        zk@.well_formed(),
    ensures
        path@.map_values(|s: String| s@) == zk_spec::zk_node_path(zk@),
{
    let mut path = Vec::new();
    path.push(new_strlit("zookeeper-operator").to_string());
    path.push(zk.metadata().name().unwrap());
    proof {
        assert_seqs_equal!(path@.map_values(|s: String| s@), zk_spec::zk_node_path(zk@));
    }
    path
}

fn zk_parent_node_path(zk: &ZookeeperCluster) -> (path: Vec<String>)
    requires
        zk@.well_formed(),
    ensures
        path@.map_values(|s: String| s@) == zk_spec::zk_parent_node_path(zk@),
{
    let mut path = Vec::new();
    path.push(new_strlit("zookeeper-operator").to_string());
    proof {
        assert_seqs_equal!(path@.map_values(|s: String| s@), zk_spec::zk_parent_node_path(zk@));
    }
    path
}

fn zk_node_data(zk: &ZookeeperCluster) -> (data: String)
    requires
        zk@.well_formed(),
    ensures
        data@ == zk_spec::zk_node_data(zk@),
{
    new_strlit("CLUSTER_SIZE=").to_string().concat(i32_to_string(zk.spec().replicas()).as_str())
}

fn make_base_labels(zk: &ZookeeperCluster) -> (labels: StringMap)
    requires
        zk@.well_formed(),
    ensures
        labels@ == zk_spec::make_base_labels(zk@),
{
    let mut labels = StringMap::empty();
    labels.insert(new_strlit("app").to_string(), zk.metadata().name().unwrap());
    labels
}

fn make_labels(zk: &ZookeeperCluster) -> (labels: StringMap)
    requires
        zk@.well_formed(),
    ensures
        labels@ == zk_spec::make_labels(zk@),
{
    let mut labels = zk.spec().labels();
    labels.extend(make_base_labels(zk));
    labels
}

fn make_headless_service_name(zk: &ZookeeperCluster) -> (name: String)
    requires
        zk@.well_formed(),
    ensures
        name@ == zk_spec::make_headless_service_name(zk@.metadata.name.get_Some_0()),
{
    zk.metadata().name().unwrap().concat(new_strlit("-headless"))
}

fn update_headless_service(zk: &ZookeeperCluster, found_headless_service: &Service) -> (headless_service: Service)
    requires
        zk@.well_formed(),
        found_headless_service@.spec.is_Some(),
    ensures
        headless_service@ == zk_spec::update_headless_service(zk@, found_headless_service@),
{
    let mut headless_service = found_headless_service.clone();
    let made_headless_service = make_headless_service(zk);
    headless_service.set_metadata({
        let mut metadata = found_headless_service.metadata();
        metadata.set_labels(made_headless_service.metadata().labels().unwrap());
        metadata.set_annotations(made_headless_service.metadata().annotations().unwrap());
        metadata
    });
    headless_service.set_spec({
        let mut spec = found_headless_service.spec().unwrap();
        spec.set_ports(made_headless_service.spec().unwrap().ports().unwrap());
        spec.set_selector(made_headless_service.spec().unwrap().selector().unwrap());
        spec
    });
    headless_service
}

/// Headless Service is used to assign DNS entry to each zookeeper server Pod
fn make_headless_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.well_formed(),
    ensures
        service@ == zk_spec::make_headless_service(zk@),
{
    let mut ports = Vec::new();

    ports.push(ServicePort::new_with(new_strlit("tcp-client").to_string(), zk.spec().ports().client()));
    ports.push(ServicePort::new_with(new_strlit("tcp-quorum").to_string(), zk.spec().ports().quorum()));
    ports.push(ServicePort::new_with(new_strlit("tcp-leader-election").to_string(), zk.spec().ports().leader_election()));
    ports.push(ServicePort::new_with(new_strlit("tcp-metrics").to_string(), zk.spec().ports().metrics()));
    ports.push(ServicePort::new_with(new_strlit("tcp-admin-server").to_string(), zk.spec().ports().admin_server()));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_headless_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, make_headless_service_name(zk), ports, false)
}

fn make_client_service_name(zk: &ZookeeperCluster) -> (name: String)
    requires
        zk@.well_formed(),
    ensures
        name@ == zk_spec::make_client_service_name(zk@.metadata.name.get_Some_0()),
{
    zk.metadata().name().unwrap().concat(new_strlit("-client"))
}

fn update_client_service(zk: &ZookeeperCluster, found_client_service: &Service) -> (client_service: Service)
    requires
        zk@.well_formed(),
        found_client_service@.spec.is_Some(),
    ensures
        client_service@ == zk_spec::update_client_service(zk@, found_client_service@),
{
    let mut client_service = found_client_service.clone();
    let made_client_service = make_client_service(zk);
    client_service.set_metadata({
        let mut metadata = found_client_service.metadata();
        metadata.set_labels(made_client_service.metadata().labels().unwrap());
        metadata.set_annotations(made_client_service.metadata().annotations().unwrap());
        metadata
    });
    client_service.set_spec({
        let mut spec = found_client_service.spec().unwrap();
        spec.set_ports(made_client_service.spec().unwrap().ports().unwrap());
        spec.set_selector(made_client_service.spec().unwrap().selector().unwrap());
        spec
    });
    client_service
}

/// Client Service is used for any client to connect to the zookeeper server
fn make_client_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.well_formed(),
    ensures
        service@ == zk_spec::make_client_service(zk@),
{
    let mut ports = Vec::new();

    ports.push(ServicePort::new_with(new_strlit("tcp-client").to_string(), zk.spec().ports().client()));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_client_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, make_client_service_name(zk), ports, true)
}

fn make_admin_server_service_name(zk: &ZookeeperCluster) -> (name: String)
    requires
        zk@.well_formed(),
    ensures
        name@ == zk_spec::make_admin_server_service_name(zk@.metadata.name.get_Some_0()),
{
    zk.metadata().name().unwrap().concat(new_strlit("-admin-server"))
}

fn update_admin_server_service(zk: &ZookeeperCluster, found_admin_server_service: &Service) -> (admin_server_service: Service)
    requires
        zk@.well_formed(),
        found_admin_server_service@.spec.is_Some(),
    ensures
        admin_server_service@ == zk_spec::update_admin_server_service(zk@, found_admin_server_service@),
{
    let mut admin_server_service = found_admin_server_service.clone();
    let made_admin_server_service = make_admin_server_service(zk);
    admin_server_service.set_metadata({
        let mut metadata = found_admin_server_service.metadata();
        metadata.set_labels(made_admin_server_service.metadata().labels().unwrap());
        metadata.set_annotations(made_admin_server_service.metadata().annotations().unwrap());
        metadata
    });
    admin_server_service.set_spec({
        let mut spec = found_admin_server_service.spec().unwrap();
        spec.set_ports(made_admin_server_service.spec().unwrap().ports().unwrap());
        spec.set_selector(made_admin_server_service.spec().unwrap().selector().unwrap());
        spec
    });
    admin_server_service
}

/// Admin-server Service is used for client to connect to admin server
fn make_admin_server_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.well_formed(),
    ensures
        service@ == zk_spec::make_admin_server_service(zk@),
{
    let mut ports = Vec::new();

    ports.push(ServicePort::new_with(new_strlit("tcp-admin-server").to_string(), zk.spec().ports().admin_server()));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_admin_server_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, make_admin_server_service_name(zk), ports, true)
}

/// make_service constructs the Service object given the name, ports and cluster_ip
fn make_service(zk: &ZookeeperCluster, name: String, ports: Vec<ServicePort>, cluster_ip: bool) -> (service: Service)
    requires
        zk@.well_formed(),
    ensures
        service@ == zk_spec::make_service(zk@, name@, ports@.map_values(|port: ServicePort| port@), cluster_ip),
{
    let mut service = Service::default();
    service.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(name);
        metadata.set_labels(make_labels(zk));
        metadata.set_annotations(zk.spec().annotations());
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(zk.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    zk_spec::make_service(zk@, name@, ports@.map_values(|port: ServicePort| port@), cluster_ip).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    service.set_spec({
        let mut service_spec = ServiceSpec::default();
        if !cluster_ip {
            service_spec.set_cluster_ip(new_strlit("None").to_string());
        }
        service_spec.set_ports(ports);
        service_spec.set_selector(make_base_labels(zk));
        service_spec
    });

    service
}

fn make_config_map_name(zk: &ZookeeperCluster) -> (name: String)
    requires
        zk@.well_formed(),
    ensures
        name@ == zk_spec::make_config_map_name(zk@.metadata.name.get_Some_0()),
{
    zk.metadata().name().unwrap().concat(new_strlit("-configmap"))
}

fn update_config_map(zk: &ZookeeperCluster, found_config_map: &ConfigMap) -> (config_map: ConfigMap)
    requires
        zk@.well_formed(),
    ensures
        config_map@ == zk_spec::update_config_map(zk@, found_config_map@),
{
    let mut config_map = found_config_map.clone();
    let made_config_map = make_config_map(zk);
    config_map.set_metadata({
        let mut metadata = found_config_map.metadata();
        metadata.set_labels(made_config_map.metadata().labels().unwrap());
        metadata.set_annotations(made_config_map.metadata().annotations().unwrap());
        metadata
    });
    config_map.set_data(made_config_map.data().unwrap());
    config_map
}

/// The ConfigMap stores the configuration data of zookeeper servers
fn make_config_map(zk: &ZookeeperCluster) -> (config_map: ConfigMap)
    requires
        zk@.well_formed(),
    ensures
        config_map@ == zk_spec::make_config_map(zk@),
{
    let mut config_map = ConfigMap::default();

    config_map.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_config_map_name(zk));
        metadata.set_labels(make_labels(zk));
        metadata.set_annotations(zk.spec().annotations());
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(zk.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    zk_spec::make_config_map(zk@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    config_map.set_data({
        let mut data = StringMap::empty();
        data.insert(new_strlit("zoo.cfg").to_string(), make_zk_config(zk));
        data.insert(new_strlit("log4j.properties").to_string(), make_log4j_config());
        data.insert(new_strlit("log4j-quiet.properties").to_string(), make_log4j_quiet_config());
        data.insert(new_strlit("env.sh").to_string(), make_env_config(zk));
        data
    });

    config_map
}

fn make_zk_config(zk: &ZookeeperCluster) -> (s: String)
    ensures
        s@ == zk_spec::make_zk_config(zk@),
{
    new_strlit(
        "4lw.commands.whitelist=cons, envi, conf, crst, srvr, stat, mntr, ruok\n\
        dataDir=/data\n\
        standaloneEnabled=false\n\
        reconfigEnabled=true\n\
        skipACL=yes\n\
        metricsProvider.className=org.apache.zookeeper.metrics.prometheus.PrometheusMetricsProvider\n\
        metricsProvider.httpPort=").to_string().concat(i32_to_string(zk.spec().ports().metrics()).as_str()).concat(new_strlit("\n\
        metricsProvider.exportJvmInfo=true\n\
        initLimit=")).concat(i32_to_string(zk.spec().conf().init_limit()).as_str()).concat(new_strlit("\n\
        syncLimit=")).concat(i32_to_string(zk.spec().conf().sync_limit()).as_str()).concat(new_strlit("\n\
        tickTime=")).concat(i32_to_string(zk.spec().conf().tick_time()).as_str()).concat(new_strlit("\n\
        globalOutstandingLimit=")).concat(i32_to_string(zk.spec().conf().global_outstanding_limit()).as_str()).concat(new_strlit("\n\
        preAllocSize=")).concat(i32_to_string(zk.spec().conf().pre_alloc_size()).as_str()).concat(new_strlit("\n\
        snapCount=")).concat(i32_to_string(zk.spec().conf().snap_count()).as_str()).concat(new_strlit("\n\
        commitLogCount=")).concat(i32_to_string(zk.spec().conf().commit_log_count()).as_str()).concat(new_strlit("\n\
        snapSizeLimitInKb=")).concat(i32_to_string(zk.spec().conf().snap_size_limit_in_kb()).as_str()).concat(new_strlit("\n\
        maxCnxns=")).concat(i32_to_string(zk.spec().conf().max_cnxns()).as_str()).concat(new_strlit("\n\
        maxClientCnxns=")).concat(i32_to_string(zk.spec().conf().max_client_cnxns()).as_str()).concat(new_strlit("\n\
        minSessionTimeout=")).concat(i32_to_string(zk.spec().conf().min_session_timeout()).as_str()).concat(new_strlit("\n\
        maxSessionTimeout=")).concat(i32_to_string(zk.spec().conf().max_session_timeout()).as_str()).concat(new_strlit("\n\
        autopurge.snapRetainCount=")).concat(i32_to_string(zk.spec().conf().auto_purge_snap_retain_count()).as_str()).concat(new_strlit("\n\
        autopurge.purgeInterval=")).concat(i32_to_string(zk.spec().conf().auto_purge_purge_interval()).as_str()).concat(new_strlit("\n\
        quorumListenOnAllIPs=")).concat(bool_to_string(zk.spec().conf().quorum_listen_on_all_ips()).as_str()).concat(new_strlit("\n\
        admin.serverPort=")).concat(i32_to_string(zk.spec().ports().admin_server()).as_str()).concat(new_strlit("\n\
        dynamicConfigFile=/data/zoo.cfg.dynamic\n"
    ))
}

fn make_log4j_config() -> (s: String)
    ensures
        s@ == zk_spec::make_log4j_config(),
{
    new_strlit(
        "zookeeper.root.logger=CONSOLE\n\
        zookeeper.console.threshold=INFO\n\
        log4j.rootLogger=${zookeeper.root.logger}\n\
        log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n\
        log4j.appender.CONSOLE.Threshold=${zookeeper.console.threshold}\n\
        log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n\
        log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    ).to_string()
}

fn make_log4j_quiet_config() -> (s: String)
    ensures
        s@ == zk_spec::make_log4j_quiet_config(),
{
    new_strlit(
        "log4j.rootLogger=ERROR, CONSOLE\n\
        log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n\
        log4j.appender.CONSOLE.Threshold=ERROR\n\
        log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n\
        log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    ).to_string()
}

fn make_env_config(zk: &ZookeeperCluster) -> (s: String)
    requires
        zk@.well_formed(),
    ensures
        s@ == zk_spec::make_env_config(zk@),
{
    let name = zk.metadata().name().unwrap();
    let namespace = zk.metadata().namespace().unwrap();
    let client_port = i32_to_string(zk.spec().ports().client());
    let quorum_port = i32_to_string(zk.spec().ports().quorum());
    let leader_election_port = i32_to_string(zk.spec().ports().leader_election());
    let admin_server_port = i32_to_string(zk.spec().ports().admin_server());

    new_strlit(
        "#!/usr/bin/env bash\n\n\
        DOMAIN=").to_string().concat(name.as_str()).concat(new_strlit("-headless.")).concat(namespace.as_str())
            .concat(new_strlit(".svc.cluster.local\n\
        QUORUM_PORT=")).concat(quorum_port.as_str()).concat(new_strlit("\n\
        LEADER_PORT=")).concat(leader_election_port.as_str()).concat(new_strlit("\n\
        CLIENT_HOST=")).concat(name.as_str()).concat(new_strlit("-client\n\
        CLIENT_PORT=")).concat(client_port.as_str()).concat(new_strlit("\n\
        ADMIN_SERVER_HOST=")).concat(name.as_str()).concat(new_strlit("-admin-server\n\
        ADMIN_SERVER_PORT=")).concat(admin_server_port.as_str()).concat(new_strlit("\n\
        CLUSTER_NAME=")).concat(name.as_str()).concat(new_strlit("\n"))
}

fn make_stateful_set_name(zk: &ZookeeperCluster) -> (name: String)
    requires
        zk@.well_formed(),
    ensures
        name@ == zk_spec::make_stateful_set_name(zk@.metadata.name.get_Some_0()),
{
    zk.metadata().name().unwrap()
}

fn update_stateful_set(zk: &ZookeeperCluster, found_stateful_set: &StatefulSet, rv: &String) -> (stateful_set: StatefulSet)
    requires
        zk@.well_formed(),
        found_stateful_set@.spec.is_Some(),
    ensures
        stateful_set@ == zk_spec::update_stateful_set(zk@, found_stateful_set@, rv@),
{
    let mut stateful_set = found_stateful_set.clone();
    let made_stateful_set = make_stateful_set(zk, rv);
    stateful_set.set_metadata({
        let mut metadata = found_stateful_set.metadata();
        metadata.set_labels(made_stateful_set.metadata().labels().unwrap());
        metadata.set_annotations(made_stateful_set.metadata().annotations().unwrap());
        metadata
    });
    stateful_set.set_spec({
        let mut spec = found_stateful_set.spec().unwrap();
        spec.set_replicas(made_stateful_set.spec().unwrap().replicas().unwrap());
        spec.set_template(made_stateful_set.spec().unwrap().template());
        spec.set_pvc_retention_policy(made_stateful_set.spec().unwrap().persistent_volume_claim_retention_policy().unwrap());
        spec
    });
    stateful_set
}

/// The StatefulSet manages the zookeeper server containers (as Pods)
/// and the volumes attached to each server (as PersistentVolumeClaims)
fn make_stateful_set(zk: &ZookeeperCluster, rv: &String) -> (stateful_set: StatefulSet)
    requires
        zk@.well_formed(),
    ensures
        stateful_set@ == zk_spec::make_stateful_set(zk@, rv@),
{
    let mut stateful_set = StatefulSet::default();
    stateful_set.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_stateful_set_name(zk));
        metadata.set_labels(make_labels(zk));
        metadata.set_annotations(zk.spec().annotations());
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(zk.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    zk_spec::make_stateful_set(zk@, rv@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    stateful_set.set_spec({
        let mut stateful_set_spec = StatefulSetSpec::default();
        // Set the replica number
        stateful_set_spec.set_replicas(zk.spec().replicas());
        // Set the headless service to assign DNS entry to each zookeeper server
        stateful_set_spec.set_service_name(zk.metadata().name().unwrap().concat(new_strlit("-headless")));
        // Set the selector used for querying pods of this stateful set
        stateful_set_spec.set_selector({
            let mut selector = LabelSelector::default();
            selector.set_match_labels(make_base_labels(zk));
            selector
        });
        stateful_set_spec.set_pvc_retention_policy({
            let mut policy = StatefulSetPersistentVolumeClaimRetentionPolicy::default();
            policy.set_when_deleted(new_strlit("Delete").to_string());
            policy.set_when_scaled(new_strlit("Delete").to_string());
            policy
        });
        // Set the template used for creating pods
        stateful_set_spec.set_template({
            let mut pod_template_spec = PodTemplateSpec::default();
            pod_template_spec.set_metadata({
                let mut metadata = ObjectMeta::default();
                metadata.set_generate_name(zk.metadata().name().unwrap());
                metadata.set_labels(make_labels(zk));
                metadata.set_annotations({
                    let mut annotations = zk.spec().annotations();
                    annotations.insert(new_strlit("config").to_string(), rv.clone());
                    annotations
                });
                metadata
            });
            pod_template_spec.set_spec(make_zk_pod_spec(zk));
            pod_template_spec
        });
        // Set the templates used for creating the persistent volume claims attached to each pod
        stateful_set_spec.set_volume_claim_templates({
            if zk.spec().persistence().enabled() {
                let mut volume_claim_templates = Vec::new();
                volume_claim_templates.push({
                    let mut pvc = PersistentVolumeClaim::default();
                    pvc.set_metadata({
                        let mut metadata = ObjectMeta::default();
                        metadata.set_name(new_strlit("data").to_string());
                        metadata.set_labels(make_base_labels(zk));
                        metadata
                    });
                    pvc.set_spec({
                        let mut pvc_spec = PersistentVolumeClaimSpec::default();
                        pvc_spec.set_access_modes({
                            let mut access_modes = Vec::new();
                            access_modes.push(new_strlit("ReadWriteOnce").to_string());
                            proof {
                                assert_seqs_equal!(
                                    access_modes@.map_values(|mode: String| mode@),
                                    zk_spec::make_stateful_set(zk@, rv@)
                                        .spec.get_Some_0().volume_claim_templates.get_Some_0()[0]
                                        .spec.get_Some_0().access_modes.get_Some_0()
                                );
                            }
                            access_modes
                        });
                        pvc_spec.set_resources({
                            let mut resources = ResourceRequirements::default();
                            resources.set_requests({
                                let mut requests = StringMap::empty();
                                requests.insert(new_strlit("storage").to_string(), zk.spec().persistence().storage_size());
                                requests
                            });
                            resources
                        });
                        pvc_spec.overwrite_storage_class_name(zk.spec().persistence().storage_class_name());
                        pvc_spec
                    });
                    pvc
                });
                proof {
                    assert_seqs_equal!(
                        volume_claim_templates@.map_values(|pvc: PersistentVolumeClaim| pvc@),
                        zk_spec::make_stateful_set(zk@, rv@).spec.get_Some_0().volume_claim_templates.get_Some_0()
                    );
                }
                volume_claim_templates
            } else {
                let empty_templates = Vec::<PersistentVolumeClaim>::new();
                proof {
                    assert_seqs_equal!(
                        empty_templates@.map_values(|pvc: PersistentVolumeClaim| pvc@),
                        zk_spec::make_stateful_set(zk@, rv@).spec.get_Some_0().volume_claim_templates.get_Some_0()
                    );
                }
                empty_templates
            }
        });
        stateful_set_spec
    });
    stateful_set
}

fn make_zk_pod_spec(zk: &ZookeeperCluster) -> (pod_spec: PodSpec)
    requires
        zk@.well_formed(),
    ensures
        pod_spec@ == zk_spec::make_zk_pod_spec(zk@),
{
    let mut pod_spec = PodSpec::default();

    pod_spec.overwrite_affinity(zk.spec().affinity());
    pod_spec.set_containers({
        let mut containers = Vec::new();
        containers.push({
            let mut zk_container = Container::default();
            zk_container.set_name(new_strlit("zookeeper").to_string());
            zk_container.set_image(zk.spec().image());
            zk_container.set_command({
                let mut command = Vec::new();
                command.push(new_strlit("/usr/local/bin/zookeeperStart.sh").to_string());
                proof {
                    let spec_cmd = seq![new_strlit("/usr/local/bin/zookeeperStart.sh")@];
                    assert_seqs_equal!(command@.map_values(|s: String| s@), spec_cmd);
                }
                command
            });
            zk_container.set_lifecycle({
                let mut lifecycle = Lifecycle::default();
                lifecycle.set_pre_stop({
                    let mut pre_stop = LifecycleHandler::default();
                    pre_stop.set_exec({
                        let mut exec = ExecAction::default();
                        exec.set_command({
                            let mut command = Vec::new();
                            command.push(new_strlit("zookeeperTeardown.sh").to_string());

                            proof {
                                assert_seqs_equal!(
                                    command@.map_values(|s: String| s@),
                                    zk_spec::make_zk_pod_spec(zk@).containers[0].lifecycle.get_Some_0().pre_stop.get_Some_0().exec_.get_Some_0().command.get_Some_0()
                                );
                            }

                            command
                        });
                        exec
                    });
                    pre_stop
                });
                lifecycle
            });
            zk_container.set_image_pull_policy(new_strlit("Always").to_string());
            zk_container.overwrite_resources(zk.spec().resources());
            zk_container.set_volume_mounts({
                let mut volume_mounts = Vec::new();
                volume_mounts.push({
                    let mut data_volume_mount = VolumeMount::default();
                    data_volume_mount.set_name(new_strlit("data").to_string());
                    data_volume_mount.set_mount_path(new_strlit("/data").to_string());
                    data_volume_mount
                });
                volume_mounts.push({
                    let mut conf_volume_mount = VolumeMount::default();
                    conf_volume_mount.set_name(new_strlit("conf").to_string());
                    conf_volume_mount.set_mount_path(new_strlit("/conf").to_string());
                    conf_volume_mount
                });

                proof {
                    assert_seqs_equal!(
                        volume_mounts@.map_values(|volume_mount: VolumeMount| volume_mount@),
                        zk_spec::make_zk_pod_spec(zk@).containers[0].volume_mounts.get_Some_0()
                    );
                }

                volume_mounts
            });
            zk_container.set_ports({
                let mut ports = Vec::new();
                ports.push(ContainerPort::new_with(new_strlit("client").to_string(), zk.spec().ports().client()));
                ports.push(ContainerPort::new_with(new_strlit("quorum").to_string(), zk.spec().ports().quorum()));
                ports.push(ContainerPort::new_with(new_strlit("leader-election").to_string(), zk.spec().ports().leader_election()));
                ports.push(ContainerPort::new_with(new_strlit("metrics").to_string(), zk.spec().ports().metrics()));
                ports.push(ContainerPort::new_with(new_strlit("admin-server").to_string(), zk.spec().ports().admin_server()));

                proof {
                    assert_seqs_equal!(
                        ports@.map_values(|port: ContainerPort| port@),
                        zk_spec::make_zk_pod_spec(zk@).containers[0].ports.get_Some_0()
                    );
                }

                ports
            });
            zk_container.set_readiness_probe({
                let mut probe = Probe::default();
                probe.set_exec({
                    let mut exec = ExecAction::default();
                    exec.set_command({
                        let mut command = Vec::new();
                        command.push(new_strlit("zookeeperReady.sh").to_string());

                        proof {
                            assert_seqs_equal!(
                                command@.map_values(|s: String| s@),
                                zk_spec::make_zk_pod_spec(zk@).containers[0].readiness_probe.get_Some_0().exec_.get_Some_0().command.get_Some_0()
                            );
                        }

                        command
                    });
                    exec
                });
                probe.set_failure_threshold(3);
                probe.set_initial_delay_seconds(10);
                probe.set_period_seconds(10);
                probe.set_success_threshold(1);
                probe.set_timeout_seconds(10);
                probe
            });
            zk_container.set_liveness_probe({
                let mut probe = Probe::default();
                probe.set_exec({
                    let mut exec = ExecAction::default();
                    exec.set_command({
                        let mut command = Vec::new();
                        command.push(new_strlit("zookeeperLive.sh").to_string());

                        proof {
                            assert_seqs_equal!(
                                command@.map_values(|s: String| s@),
                                zk_spec::make_zk_pod_spec(zk@).containers[0].liveness_probe.get_Some_0().exec_.get_Some_0().command.get_Some_0()
                            );
                        }

                        command
                    });
                    exec
                });
                probe.set_failure_threshold(3);
                probe.set_initial_delay_seconds(10);
                probe.set_period_seconds(10);
                probe.set_success_threshold(1);
                probe.set_timeout_seconds(10);
                probe
            });
            zk_container
        });

        proof {
            assert_seqs_equal!(
                containers@.map_values(|container: Container| container@),
                zk_spec::make_zk_pod_spec(zk@).containers
            );
        }

        containers
    });
    pod_spec.set_volumes({
        let mut volumes = Vec::new();
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("conf").to_string());
            volume.set_config_map({
                let mut config_map = ConfigMapVolumeSource::default();
                config_map.set_name(zk.metadata().name().unwrap().concat(new_strlit("-configmap")));
                config_map
            });
            volume
        });
        if !zk.spec().persistence().enabled() {
            volumes.push({
                let mut volume = Volume::default();
                volume.set_name(new_strlit("data").to_string());
                volume.set_empty_dir(EmptyDirVolumeSource::default());
                volume
            });
        }

        proof {
            assert_seqs_equal!(
                volumes@.map_values(|vol: Volume| vol@),
                zk_spec::make_zk_pod_spec(zk@).volumes.get_Some_0()
            );
        }

        volumes
    });
    pod_spec.overwrite_tolerations(zk.spec().tolerations());
    pod_spec.set_node_selector(zk.spec().node_selector());

    pod_spec
}

}
