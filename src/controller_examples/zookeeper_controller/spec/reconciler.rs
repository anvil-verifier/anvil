// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    container::*, error::*, label_selector::*, pod_template_spec::*, prelude::*,
    resource_requirements::*, volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::{types::*, zookeeper_api::*};
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ZookeeperReconcileState {
    pub reconcile_step: ZookeeperReconcileStep,
    pub latest_config_map_rv_opt: Option<StringView>,
}

pub struct ZookeeperReconciler {}

impl Reconciler<ZookeeperClusterView, ZKAPI> for ZookeeperReconciler {
    type T = ZookeeperReconcileState;

    open spec fn reconcile_init_state() -> ZookeeperReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        zk: ZookeeperClusterView, resp_o: Option<ResponseView<ZKAPIOutputView>>, state: ZookeeperReconcileState
    ) -> (ZookeeperReconcileState, Option<RequestView<ZKAPIInputView>>) {
        reconcile_core(zk, resp_o, state)
    }

    open spec fn reconcile_done(state: ZookeeperReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: ZookeeperReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool {
        false // Don't expect anything from the user except the cr object
    }
}

pub open spec fn reconcile_init_state() -> ZookeeperReconcileState {
    ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Init,
        latest_config_map_rv_opt: None,
    }
}

pub open spec fn reconcile_done(state: ZookeeperReconcileState) -> bool {
    match state.reconcile_step {
        ZookeeperReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: ZookeeperReconcileState) -> bool {
    match state.reconcile_step {
        ZookeeperReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(
    zk: ZookeeperClusterView, resp_o: Option<ResponseView<ZKAPIOutputView>>, state: ZookeeperReconcileState
) -> (ZookeeperReconcileState, Option<RequestView<ZKAPIInputView>>)
    recommends
        zk.well_formed(),
{
    let step = state.reconcile_step;
    let resp = resp_o.get_Some_0();
    let zk_name = zk.metadata.name.get_Some_0();
    let zk_namespace = zk.metadata.namespace.get_Some_0();
    let client_port = zk.spec.ports.client;
    match step {
        ZookeeperReconcileStep::Init => {
            let req_o = APIRequest::GetRequest(GetRequest{
                key: make_headless_service_key(zk.object_ref()),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterGetHeadlessService,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        ZookeeperReconcileStep::AfterGetHeadlessService => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_headless_service_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                let unmarshal_headless_service_result = ServiceView::unmarshal(get_headless_service_resp.get_Ok_0());
                if get_headless_service_resp.is_Ok() {
                    if unmarshal_headless_service_result.is_Ok() && unmarshal_headless_service_result.get_Ok_0().spec.is_Some() {
                        // update
                        let found_headless_service = unmarshal_headless_service_result.get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: zk_namespace,
                            name: make_headless_service_name(zk_name),
                            obj: update_headless_service(zk, found_headless_service).marshal(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterUpdateHeadlessService,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_headless_service_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: zk_namespace,
                        obj: make_headless_service(zk).marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateHeadlessService,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateHeadlessService => {
            let create_headless_service_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            let unmarshal_headless_service_result = ServiceView::unmarshal(create_headless_service_resp.get_Ok_0());
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_headless_service_resp.is_Ok() && unmarshal_headless_service_result.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_client_service_key(zk.object_ref()),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetClientService,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterUpdateHeadlessService => {
            let update_headless_service_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            let unmarshal_headless_service_result = ServiceView::unmarshal(update_headless_service_resp.get_Ok_0());
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_headless_service_resp.is_Ok() && unmarshal_headless_service_result.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_client_service_key(zk.object_ref()),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetClientService,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterGetClientService => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_client_service_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                let unmarshal_client_service_result = ServiceView::unmarshal(get_client_service_resp.get_Ok_0());
                if get_client_service_resp.is_Ok() {
                    if unmarshal_client_service_result.is_Ok() && unmarshal_client_service_result.get_Ok_0().spec.is_Some() {
                        // update
                        let found_client_service = unmarshal_client_service_result.get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: zk_namespace,
                            name: make_client_service_name(zk_name),
                            obj: update_client_service(zk, found_client_service).marshal(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterUpdateClientService,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_client_service_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: zk_namespace,
                        obj: make_client_service(zk).marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateClientService,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateClientService => {
            let create_client_service_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            let unmarshal_client_service_result = ServiceView::unmarshal(create_client_service_resp.get_Ok_0());
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_client_service_resp.is_Ok() && unmarshal_client_service_result.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_admin_server_service_key(zk.object_ref()),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetAdminServerService,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterUpdateClientService => {
            let update_client_service_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            let unmarshal_client_service_result = ServiceView::unmarshal(update_client_service_resp.get_Ok_0());
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_client_service_resp.is_Ok() && unmarshal_client_service_result.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_admin_server_service_key(zk.object_ref()),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetAdminServerService,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterGetAdminServerService => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_admin_server_service_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                let unmarshal_admin_server_service_result = ServiceView::unmarshal(get_admin_server_service_resp.get_Ok_0());
                if get_admin_server_service_resp.is_Ok() {
                    if unmarshal_admin_server_service_result.is_Ok() && unmarshal_admin_server_service_result.get_Ok_0().spec.is_Some() {
                        // update
                        let found_admin_server_service = unmarshal_admin_server_service_result.get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: zk_namespace,
                            name: make_admin_server_service_name(zk_name),
                            obj: update_admin_server_service(zk, found_admin_server_service).marshal(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterUpdateAdminServerService,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_admin_server_service_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: zk_namespace,
                        obj: make_admin_server_service(zk).marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateAdminServerService,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateAdminServerService => {
            let create_admin_server_service_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            let unmarshal_admin_server_service_result = ServiceView::unmarshal(create_admin_server_service_resp.get_Ok_0());
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_admin_server_service_resp.is_Ok() && unmarshal_admin_server_service_result.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_config_map_key(zk.object_ref()),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetConfigMap,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterUpdateAdminServerService => {
            let update_admin_server_service_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            let unmarshal_admin_server_service_result = ServiceView::unmarshal(update_admin_server_service_resp.get_Ok_0());
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_admin_server_service_resp.is_Ok() && unmarshal_admin_server_service_result.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_config_map_key(zk.object_ref()),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetConfigMap,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterGetConfigMap => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_config_map_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                let unmarshal_config_map_result = ConfigMapView::unmarshal(get_config_map_resp.get_Ok_0());
                if get_config_map_resp.is_Ok() {
                    if unmarshal_config_map_result.is_Ok() {
                        // update
                        let found_config_map = unmarshal_config_map_result.get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: zk_namespace,
                            name: make_config_map_name(zk_name),
                            obj: update_config_map(zk, found_config_map).marshal(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterUpdateConfigMap,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_config_map_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: zk_namespace,
                        obj: make_config_map(zk).marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateConfigMap,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateConfigMap => {
            let create_config_map_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            let unmarshal_config_map_result = ConfigMapView::unmarshal(create_config_map_resp.get_Ok_0());
            let latest_config_map = unmarshal_config_map_result.get_Ok_0();
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_config_map_resp.is_Ok() && unmarshal_config_map_result.is_Ok()
            && latest_config_map.metadata.resource_version.is_Some() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_stateful_set_key(zk.object_ref()),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet,
                    latest_config_map_rv_opt: Some(int_to_string_view(latest_config_map.metadata.resource_version.get_Some_0())),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterUpdateConfigMap => {
            let update_config_map_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            let unmarshal_config_map_result = ConfigMapView::unmarshal(update_config_map_resp.get_Ok_0());
            let latest_config_map = unmarshal_config_map_result.get_Ok_0();
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_config_map_resp.is_Ok() && unmarshal_config_map_result.is_Ok()
            && latest_config_map.metadata.resource_version.is_Some() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_stateful_set_key(zk.object_ref()),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet,
                    latest_config_map_rv_opt: Some(int_to_string_view(latest_config_map.metadata.resource_version.get_Some_0())),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterGetStatefulSet => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_stateful_set_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                if get_stateful_set_resp.is_Ok() {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterExistsZKNode,
                        ..state
                    };
                    let node_path = seq![new_strlit("zookeeper-operator")@, zk_name];
                    let ext_req = ZKAPIInputView::ExistsRequest(
                        zk_name, zk_namespace, client_port, node_path
                    );
                    (state_prime, Some(RequestView::ExternalRequest(ext_req)))
                } else if get_stateful_set_resp.get_Err_0().is_ObjectNotFound() {
                    let req_o = APIRequest::GetRequest(GetRequest {
                        key: make_stateful_set_key(zk.object_ref()),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet2,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterExistsZKNode => {
            let exists_resp = resp.get_ExternalResponse_0().get_ExistsResponse_0().res;
            if resp_o.is_Some() && resp.is_ExternalResponse() && resp.get_ExternalResponse_0().is_ExistsResponse()
            && exists_resp.is_Ok() {
                if exists_resp.get_Ok_0().is_Some() {
                    let version = exists_resp.get_Ok_0().get_Some_0();
                    let node_path = zk_node_path(zk);
                    let data = zk_node_data(zk);
                    let ext_req = ZKAPIInputView::SetDataRequest(
                        zk_name, zk_namespace, client_port, node_path, data, version
                    );
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterUpdateZKNode,
                        ..state
                    };
                    (state_prime, Some(RequestView::ExternalRequest(ext_req)))
                } else {
                    let version = exists_resp.get_Ok_0().get_Some_0();
                    let node_path = zk_parent_node_path(zk);
                    let data = new_strlit("")@;
                    let ext_req = ZKAPIInputView::CreateRequest(
                        zk_name, zk_namespace, client_port, node_path, data
                    );
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateZKParentNode,
                        ..state
                    };
                    (state_prime, Some(RequestView::ExternalRequest(ext_req)))
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateZKParentNode => {
            let create_resp = resp.get_ExternalResponse_0().get_CreateResponse_0().res;
            if resp_o.is_Some() && resp.is_ExternalResponse() && resp.get_ExternalResponse_0().is_CreateResponse()
            && (create_resp.is_Ok() || create_resp.get_Err_0().is_ZKNodeCreateAlreadyExists()) {
                let node_path = zk_node_path(zk);
                let data = zk_node_data(zk);
                let ext_req = ZKAPIInputView::CreateRequest(
                    zk_name, zk_namespace, client_port, node_path, data
                );
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterCreateZKNode,
                    ..state
                };
                (state_prime, Some(RequestView::ExternalRequest(ext_req)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateZKNode => {
            if resp_o.is_Some() && resp.is_ExternalResponse() && resp.get_ExternalResponse_0().is_CreateResponse()
            && resp.get_ExternalResponse_0().get_CreateResponse_0().res.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_stateful_set_key(zk.object_ref()),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet2,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterUpdateZKNode => {
            if resp_o.is_Some() && resp.is_ExternalResponse() && resp.get_ExternalResponse_0().is_SetDataResponse()
            && resp.get_ExternalResponse_0().get_SetDataResponse_0().res.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_stateful_set_key(zk.object_ref()),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet2,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterGetStatefulSet2 => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse()
            && state.latest_config_map_rv_opt.is_Some() {
                let get_stateful_set_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                let unmarshal_stateful_set_result = StatefulSetView::unmarshal(get_stateful_set_resp.get_Ok_0());
                if get_stateful_set_resp.is_Ok() {
                    if unmarshal_stateful_set_result.is_Ok() {
                        let found_stateful_set = unmarshal_stateful_set_result.get_Ok_0();
                        if found_stateful_set.metadata.owner_references_only_contains(zk.controller_owner_ref())
                        && found_stateful_set.spec.is_Some() {
                            let req_o = APIRequest::UpdateRequest(UpdateRequest {
                                namespace: zk_namespace,
                                name: make_stateful_set_name(zk_name),
                                obj: update_stateful_set(zk, found_stateful_set, state.latest_config_map_rv_opt.get_Some_0()).marshal(),
                            });
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::AfterUpdateStatefulSet,
                                ..state
                            };
                            (state_prime, Some(RequestView::KRequest(req_o)))
                        } else {
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_stateful_set_resp.get_Err_0().is_ObjectNotFound() {
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: zk_namespace,
                        obj: make_stateful_set(zk, state.latest_config_map_rv_opt.get_Some_0()).marshal(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateStatefulSet,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterCreateStatefulSet => {
            let create_stateful_set_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_stateful_set_resp.is_Ok() {
                let req_o = APIRequest::UpdateStatusRequest(UpdateStatusRequest {
                    namespace: zk_namespace,
                    name: zk_name,
                    obj: update_zk_status(zk, 0).marshal(),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterUpdateStatus,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterUpdateStatefulSet => {
            let update_stateful_set_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            let unmarshal_stateful_set_result = StatefulSetView::unmarshal(update_stateful_set_resp.get_Ok_0());
            let updated_stateful_set = unmarshal_stateful_set_result.get_Ok_0();
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_stateful_set_resp.is_Ok() && unmarshal_stateful_set_result.is_Ok() {
                let ready_replicas = if updated_stateful_set.status.is_Some() && updated_stateful_set.status.get_Some_0().ready_replicas.is_Some() {
                    updated_stateful_set.status.get_Some_0().ready_replicas.get_Some_0()
                } else {
                    0
                };
                let req_o = APIRequest::UpdateStatusRequest(UpdateStatusRequest {
                    namespace: zk_namespace,
                    name: zk_name,
                    obj: update_zk_status(zk, ready_replicas).marshal(),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterUpdateStatus,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        ZookeeperReconcileStep::AfterUpdateStatus => {
            let update_status_resp = resp.get_KResponse_0().get_UpdateStatusResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateStatusResponse()
            && update_status_resp.is_Ok() {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        _ => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: step,
                ..state
            };
            (state_prime, None)
        }
    }
}

pub open spec fn reconcile_error_result(state: ZookeeperReconcileState) -> (ZookeeperReconcileState, Option<APIRequest>) {
    let state_prime = ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Error,
        ..state
    };
    (state_prime, None)
}

pub open spec fn zk_node_path(zk: ZookeeperClusterView) -> Seq<StringView>
    recommends
        zk.well_formed(),
{
    seq![new_strlit("zookeeper-operator")@, zk.metadata.name.get_Some_0()]
}

pub open spec fn zk_parent_node_path(zk: ZookeeperClusterView) -> Seq<StringView>
    recommends
        zk.well_formed(),
{
    seq![new_strlit("zookeeper-operator")@]
}

pub open spec fn zk_node_data(zk: ZookeeperClusterView) -> StringView
    recommends
        zk.well_formed(),
{
    new_strlit("CLUSTER_SIZE=")@ + int_to_string_view(zk.spec.replicas)
}

pub open spec fn update_zk_status(zk: ZookeeperClusterView, ready_replicas: int) -> ZookeeperClusterView
    recommends
        zk.well_formed(),
{
    ZookeeperClusterView {
        status: Some(ZookeeperClusterStatusView {
            ready_replicas: ready_replicas,
        }),
        ..zk
    }
}

}
