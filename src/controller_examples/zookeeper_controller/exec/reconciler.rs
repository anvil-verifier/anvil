// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, container::*, error::*, label_selector::*, object_meta::*,
    owner_reference::*, persistent_volume_claim::*, pod::*, pod_template_spec::*, prelude::*,
    resource::*, resource_requirements::*, volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vstd_ext::{string_map::*, string_view::*, to_view::*};
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
    pub latest_config_map_rv_opt: Option<String>,
}

impl ZookeeperReconcileState {
    pub open spec fn to_view(&self) -> zk_spec::ZookeeperReconcileState {
        zk_spec::ZookeeperReconcileState {
            reconcile_step: self.reconcile_step,
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
        resource_version_check(opt_response_to_view(&resp_o), opt_request_to_view(&res.1)),
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
                    let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                        api_resource: StatefulSet::api_resource(),
                        name: make_stateful_set_name(zk),
                        namespace: zk.metadata().namespace().unwrap(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet2,
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
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: StatefulSet::api_resource(),
                    name: make_stateful_set_name(zk),
                    namespace: zk.metadata().namespace().unwrap(),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet2,
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
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: StatefulSet::api_resource(),
                    name: make_stateful_set_name(zk),
                    namespace: zk.metadata().namespace().unwrap(),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet2,
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
        ZookeeperReconcileStep::AfterGetStatefulSet2 => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response()
            && state.latest_config_map_rv_opt.is_some() {
                let get_stateful_set_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_stateful_set_resp.is_ok() {
                    let unmarshal_stateful_set_result = StatefulSet::unmarshal(get_stateful_set_resp.unwrap());
                    if unmarshal_stateful_set_result.is_ok() {
                        let found_stateful_set = unmarshal_stateful_set_result.as_ref().unwrap();
                        // Only proceed if the stateful set is owned by the current cr
                        // so that we won't accidentally update ports or some other mutable fields.
                        if found_stateful_set.metadata().owner_references_only_contains(zk.controller_owner_ref())
                        && found_stateful_set.spec().is_some() {
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
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req_o)));
                        }
                    }
                } else if get_stateful_set_resp.unwrap_err().is_object_not_found() {
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
        ZookeeperReconcileStep::AfterCreateStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response() {
                let create_stateful_set_resp = resp_o.unwrap().into_k_response().into_create_response().res;
                if create_stateful_set_resp.is_ok() {
                    let updated_zk = update_zk_status(zk, 0);
                    let req_o = KubeAPIRequest::UpdateStatusRequest(KubeUpdateStatusRequest {
                        api_resource: ZookeeperCluster::api_resource(),
                        name: zk.metadata().name().unwrap(),
                        namespace: zk.metadata().namespace().unwrap(),
                        obj: updated_zk.marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterUpdateStatus,
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
        ZookeeperReconcileStep::AfterUpdateStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response() {
                let update_stateful_set_resp = resp_o.unwrap().into_k_response().into_update_response().res;
                if update_stateful_set_resp.is_ok() {
                    let unmarshal_stateful_set_result = StatefulSet::unmarshal(update_stateful_set_resp.unwrap());
                    if unmarshal_stateful_set_result.is_ok() {
                        let updated_stateful_set = unmarshal_stateful_set_result.unwrap();
                        let ready_replicas = if updated_stateful_set.status().is_some() && updated_stateful_set.status().as_ref().unwrap().ready_replicas().is_some() {
                            updated_stateful_set.status().as_ref().unwrap().ready_replicas().unwrap()
                        } else {
                            0
                        };
                        let updated_zk = update_zk_status(zk, ready_replicas);
                        let req_o = KubeAPIRequest::UpdateStatusRequest(KubeUpdateStatusRequest {
                            api_resource: ZookeeperCluster::api_resource(),
                            name: zk.metadata().name().unwrap(),
                            namespace: zk.metadata().namespace().unwrap(),
                            obj: updated_zk.marshal(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterUpdateStatus,
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

fn update_zk_status(zk: &ZookeeperCluster, ready_replicas: i32) -> (updated_zk: ZookeeperCluster)
    ensures
        updated_zk@ == zk_spec::update_zk_status(zk@, ready_replicas as int),
{
    let mut updated_zk = zk.clone();
    updated_zk.set_status({
        let mut status = ZookeeperClusterStatus::default();
        status.set_ready_replicas(ready_replicas);
        status
    });
    updated_zk
}

}
