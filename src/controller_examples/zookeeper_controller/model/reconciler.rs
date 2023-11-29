// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
use crate::zookeeper_controller::model::resource::*;
use crate::zookeeper_controller::trusted::{
    maker::*, spec_types::*, step::*, zookeeper_api_spec::*,
};
use vstd::prelude::*;
use vstd::string::*;

verus! {

impl Reconciler<ZookeeperClusterView, ZKAPI> for ZookeeperReconciler {
    type T = ZookeeperReconcileState;

    open spec fn reconcile_init_state() -> ZookeeperReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(zk: ZookeeperClusterView, resp_o: Option<ResponseView<ZKAPIOutputView>>, state: ZookeeperReconcileState)
    -> (ZookeeperReconcileState, Option<RequestView<ZKAPIInputView>>) {
        reconcile_core(zk, resp_o, state)
    }

    open spec fn reconcile_done(state: ZookeeperReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: ZookeeperReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool { false /* Don't expect anything from the user except the cr object */ }
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

pub open spec fn reconcile_core(zk: ZookeeperClusterView, resp_o: Option<ResponseView<ZKAPIOutputView>>, state: ZookeeperReconcileState) -> (ZookeeperReconcileState, Option<RequestView<ZKAPIInputView>>) {
    let step = state.reconcile_step;
    let resp = resp_o.get_Some_0();
    let zk_name = zk.metadata.name.get_Some_0();
    let zk_namespace = zk.metadata.namespace.get_Some_0();
    let client_port = zk.spec.ports.client;
    match step {
        ZookeeperReconcileStep::Init => {
            let req_o = APIRequest::GetRequest(HeadlessServiceBuilder::get_request(zk));
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::HeadlessService),
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        ZookeeperReconcileStep::AfterKRequestStep(_, resource) => {
            match resource {
                SubResource::HeadlessService => { reconcile_helper::<HeadlessServiceBuilder>(zk, resp_o, state) },
                SubResource::ClientService => { reconcile_helper::<ClientServiceBuilder>(zk, resp_o, state) },
                SubResource::AdminServerService => { reconcile_helper::<AdminServerServiceBuilder>(zk, resp_o, state) },
                SubResource::ConfigMap => { reconcile_helper::<ConfigMapBuilder>(zk, resp_o, state) },
                SubResource::StatefulSet => { reconcile_helper::<StatefulSetBuilder>(zk, resp_o, state) },
            }
        },
        ZookeeperReconcileStep::AfterExistsStatefulSet => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_stateful_set_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                if get_stateful_set_resp.is_Ok() {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterExistsZKNode,
                        ..state
                    };
                    (state_prime, Some(RequestView::ExternalRequest(zk_exists_request(zk))))
                } else if get_stateful_set_resp.get_Err_0().is_ObjectNotFound() {
                    let req_o = APIRequest::GetRequest(StatefulSetBuilder::get_request(zk));
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::StatefulSet),
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
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterUpdateZKNode,
                        ..state
                    };
                    (state_prime, Some(RequestView::ExternalRequest(zk_set_data_request(zk, exists_resp.get_Ok_0().get_Some_0()))))
                } else {
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateZKParentNode,
                        ..state
                    };
                    (state_prime, Some(RequestView::ExternalRequest(zk_create_parent_node_request(zk))))
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
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterCreateZKNode,
                    ..state
                };
                (state_prime, Some(RequestView::ExternalRequest(zk_create_node_request(zk))))
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
                let req_o = APIRequest::GetRequest(StatefulSetBuilder::get_request(zk));
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::StatefulSet),
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
                let req_o = APIRequest::GetRequest(StatefulSetBuilder::get_request(zk));
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::StatefulSet),
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

pub open spec fn zk_node_path(zk: ZookeeperClusterView) -> Seq<StringView> {
    seq![new_strlit("zookeeper-operator")@, zk.metadata.name.get_Some_0()]
}

pub open spec fn zk_parent_node_path(zk: ZookeeperClusterView) -> Seq<StringView> {
    seq![new_strlit("zookeeper-operator")@]
}

pub open spec fn zk_node_data(zk: ZookeeperClusterView) -> StringView {
    new_strlit("CLUSTER_SIZE=")@ + int_to_string_view(zk.spec.replicas)
}

pub open spec fn zk_exists_request(zk: ZookeeperClusterView) -> ZKAPIInputView {
    let zk_name = zk.metadata.name.get_Some_0();
    let zk_namespace = zk.metadata.namespace.get_Some_0();
    let client_port = zk.spec.ports.client;
    let node_path = zk_node_path(zk);
    ZKAPIInputView::ExistsRequest(zk_name, zk_namespace, client_port, node_path)
}

pub open spec fn zk_set_data_request(zk: ZookeeperClusterView, version: int) -> ZKAPIInputView {
    let zk_name = zk.metadata.name.get_Some_0();
    let zk_namespace = zk.metadata.namespace.get_Some_0();
    let client_port = zk.spec.ports.client;
    let node_path = zk_node_path(zk);
    let data = zk_node_data(zk);
    ZKAPIInputView::SetDataRequest(zk_name, zk_namespace, client_port, node_path, data, version)
}

pub open spec fn zk_create_parent_node_request(zk: ZookeeperClusterView) -> ZKAPIInputView {
    let zk_name = zk.metadata.name.get_Some_0();
    let zk_namespace = zk.metadata.namespace.get_Some_0();
    let client_port = zk.spec.ports.client;
    let node_path = zk_parent_node_path(zk);
    let data = new_strlit("")@;
    ZKAPIInputView::CreateRequest(zk_name, zk_namespace, client_port, node_path, data)
}

pub open spec fn zk_create_node_request(zk: ZookeeperClusterView) -> ZKAPIInputView {
    let zk_name = zk.metadata.name.get_Some_0();
    let zk_namespace = zk.metadata.namespace.get_Some_0();
    let client_port = zk.spec.ports.client;
    let node_path = zk_node_path(zk);
    let data = zk_node_data(zk);
    ZKAPIInputView::CreateRequest(zk_name, zk_namespace, client_port, node_path, data)
}

pub open spec fn reconcile_helper<Builder: ResourceBuilder<ZookeeperClusterView, ZookeeperReconcileState>>(
    zk: ZookeeperClusterView, resp_o: Option<ResponseView<ZKAPIOutputView>>, state: ZookeeperReconcileState
) -> (ZookeeperReconcileState, Option<RequestView<ZKAPIInputView>>) {
    let step = state.reconcile_step;
    match step {
        ZookeeperReconcileStep::AfterKRequestStep(action, resource) => {
            match action {
                ActionKind::Get => {
                    if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                        let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                        if get_resp.is_Ok() {
                            // update
                            let new_obj = Builder::update(zk, state, get_resp.get_Ok_0());
                            if new_obj.is_Ok() {
                                let updated_obj = new_obj.get_Ok_0();
                                let req_o = APIRequest::UpdateRequest(UpdateRequest {
                                    namespace: zk.metadata.namespace.get_Some_0(),
                                    name: Builder::get_request(zk).key.name,
                                    obj: updated_obj,
                                });
                                let state_prime = ZookeeperReconcileState {
                                    reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Update, resource),
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
                        } else if get_resp.get_Err_0().is_ObjectNotFound() {
                            let new_obj = Builder::make(zk, state);
                            if new_obj.is_Ok() {
                                let req_o = APIRequest::CreateRequest(CreateRequest {
                                    namespace: zk.metadata.namespace.get_Some_0(),
                                    obj: new_obj.get_Ok_0(),
                                });
                                let state_prime = ZookeeperReconcileState {
                                    reconcile_step: ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Create, resource),
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
                    } else {
                        // return error state
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                },
                ActionKind::Create => {
                    let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
                    if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
                    && create_resp.is_Ok() {
                        let next_state = Builder::state_after_create(zk, create_resp.get_Ok_0(), state);
                        if next_state.is_Ok() {
                            let (state_prime, req) = next_state.get_Ok_0();
                            let req_o = if req.is_Some() { Some(RequestView::KRequest(req.get_Some_0())) } else { None };
                            (state_prime, req_o)
                        } else {
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        // return error state
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                },
                ActionKind::Update => {
                    let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
                    if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
                    && update_resp.is_Ok() {
                        let next_state = Builder::state_after_update(zk, update_resp.get_Ok_0(), state);
                        if next_state.is_Ok() {
                            let (state_prime, req) = next_state.get_Ok_0();
                            let req_o = if req.is_Some() { Some(RequestView::KRequest(req.get_Some_0())) } else { None };
                            (state_prime, req_o)
                        } else {
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        // return error state
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                },
            }
        },
        _ => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            (state_prime, None)
        },
    }
}

pub struct ZookeeperMaker {}

impl Maker for ZookeeperMaker {
    open spec fn make_headless_service_key(zookeeper: ZookeeperClusterView) -> ObjectRef { make_headless_service_key(zookeeper) }

    open spec fn make_client_service_key(zookeeper: ZookeeperClusterView) -> ObjectRef { make_client_service_key(zookeeper) }

    open spec fn make_admin_server_service_key(zookeeper: ZookeeperClusterView) -> ObjectRef { make_admin_server_service_key(zookeeper) }

    open spec fn make_config_map_key(zookeeper: ZookeeperClusterView) -> ObjectRef { make_config_map_key(zookeeper) }

    open spec fn make_stateful_set_key(zookeeper: ZookeeperClusterView) -> ObjectRef { make_stateful_set_key(zookeeper) }

    open spec fn make_headless_service(zookeeper: ZookeeperClusterView) -> ServiceView { make_headless_service(zookeeper) }

    open spec fn make_client_service(zookeeper: ZookeeperClusterView) -> ServiceView { make_client_service(zookeeper) }

    open spec fn make_admin_server_service(zookeeper: ZookeeperClusterView) -> ServiceView { make_admin_server_service(zookeeper) }

    open spec fn make_config_map(zookeeper: ZookeeperClusterView) -> ConfigMapView { make_config_map(zookeeper) }

    open spec fn make_stateful_set(zookeeper: ZookeeperClusterView, config_map_rv: StringView) -> StatefulSetView { make_stateful_set(zookeeper, config_map_rv) }
}

}
