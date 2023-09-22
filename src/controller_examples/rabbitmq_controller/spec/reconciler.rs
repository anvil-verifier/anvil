// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::resource::*;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RabbitmqReconciler {}

impl Reconciler<RabbitmqClusterView, EmptyAPI> for RabbitmqReconciler {
    type T = RabbitmqReconcileState;

    open spec fn reconcile_init_state() -> RabbitmqReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        rabbitmq: RabbitmqClusterView, resp_o: Option<ResponseView<EmptyTypeView>>, state: RabbitmqReconcileState
    ) -> (RabbitmqReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(rabbitmq, resp_o, state)
    }

    open spec fn reconcile_done(state: RabbitmqReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: RabbitmqReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool {
        false // Don't expect anything from the user except the cr object
    }
}

pub open spec fn reconcile_init_state() -> RabbitmqReconcileState {
    RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Init,
        latest_config_map_rv_opt: None,
    }
}

pub open spec fn reconcile_done(state: RabbitmqReconcileState) -> bool {
    match state.reconcile_step {
        RabbitmqReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: RabbitmqReconcileState) -> bool {
    match state.reconcile_step {
        RabbitmqReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(
    rabbitmq: RabbitmqClusterView, resp_o: Option<ResponseView<EmptyTypeView>>, state: RabbitmqReconcileState
) -> (RabbitmqReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let step = state.reconcile_step;
    match step{
        RabbitmqReconcileStep::Init => {
            // get headless service
            let req_o = APIRequest::GetRequest(GetRequest{
                key: make_headless_service_key(rabbitmq)
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterGetHeadlessService,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        RabbitmqReconcileStep::AfterGetHeadlessService => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let made_obj = make_headless_service(rabbitmq);
                let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_resp.is_Ok() {
                    // update
                    if ServiceView::unmarshal(get_resp.get_Ok_0()).is_Ok()
                    {
                        let found_obj = ServiceView::unmarshal(get_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            name: make_headless_service_name(rabbitmq),
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            obj: update_headless_service(rabbitmq, found_obj).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateHeadlessService,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: made_obj.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateHeadlessService,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateHeadlessService => {
            let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_obj = ServiceView::unmarshal(create_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_main_service_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetService,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdateHeadlessService => {
            let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_obj = ServiceView::unmarshal(update_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_main_service_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetService,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterGetService => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let made_obj = make_main_service(rabbitmq);
                let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_resp.is_Ok() {
                    // update
                    if ServiceView::unmarshal(get_resp.get_Ok_0()).is_Ok()
                    {
                        let found_obj = ServiceView::unmarshal(get_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            name: make_main_service_name(rabbitmq),
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            obj: update_main_service(rabbitmq, found_obj).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateService,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: made_obj.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateService,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateService => {
            let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_obj = ServiceView::unmarshal(create_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_erlang_secret_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetErlangCookieSecret,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdateService => {
            let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_obj = ServiceView::unmarshal(update_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_erlang_secret_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetErlangCookieSecret,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterGetErlangCookieSecret => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let made_obj = make_erlang_secret(rabbitmq);
                let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_resp.is_Ok() {
                    // update
                    if SecretView::unmarshal(get_resp.get_Ok_0()).is_Ok()
                    {
                        let found_obj = SecretView::unmarshal(get_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            name: make_erlang_secret_name(rabbitmq),
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            obj: update_erlang_secret(rabbitmq, found_obj).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateErlangCookieSecret,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: made_obj.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateErlangCookieSecret,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateErlangCookieSecret => {
            let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_obj = SecretView::unmarshal(create_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_default_user_secret_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetDefaultUserSecret,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdateErlangCookieSecret => {
            let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_obj = SecretView::unmarshal(update_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_default_user_secret_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetDefaultUserSecret,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterGetDefaultUserSecret => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let made_obj = make_default_user_secret(rabbitmq);
                let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_resp.is_Ok() {
                    // update
                    if SecretView::unmarshal(get_resp.get_Ok_0()).is_Ok()
                    {
                        let found_obj = SecretView::unmarshal(get_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            name: make_default_user_secret_name(rabbitmq),
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            obj: update_default_user_secret(rabbitmq, found_obj).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateDefaultUserSecret,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: made_obj.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateDefaultUserSecret,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateDefaultUserSecret => {
            let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_obj = SecretView::unmarshal(create_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_plugins_config_map_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetPluginsConfigMap,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdateDefaultUserSecret => {
            let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_obj = SecretView::unmarshal(update_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_plugins_config_map_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetPluginsConfigMap,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterGetPluginsConfigMap => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let made_obj = make_plugins_config_map(rabbitmq);
                let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_resp.is_Ok() {
                    // update
                    if ConfigMapView::unmarshal(get_resp.get_Ok_0()).is_Ok()
                    {
                        let found_obj = ConfigMapView::unmarshal(get_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            name: make_plugins_config_map_name(rabbitmq),
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            obj: update_plugins_config_map(rabbitmq, found_obj).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdatePluginsConfigMap,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: made_obj.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreatePluginsConfigMap,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreatePluginsConfigMap => {
            let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_obj = ConfigMapView::unmarshal(create_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_server_config_map_key(rabbitmq.object_ref()),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetServerConfigMap,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdatePluginsConfigMap => {
            let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_obj = ConfigMapView::unmarshal(update_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_server_config_map_key(rabbitmq.object_ref()),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetServerConfigMap,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterGetServerConfigMap => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let config_map = make_server_config_map(rabbitmq);
                let get_config_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_config_resp.is_Ok() {
                    // update
                    if ConfigMapView::unmarshal(get_config_resp.get_Ok_0()).is_Ok()
                    {
                        let found_config_map = ConfigMapView::unmarshal(get_config_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            name: make_server_config_map_name(rabbitmq.metadata.name.get_Some_0()),
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            obj: update_server_config_map(rabbitmq, found_config_map).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateServerConfigMap,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_config_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: config_map.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateServerConfigMap,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateServerConfigMap => {
            let create_cm_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_cm = ConfigMapView::unmarshal(create_cm_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_cm_resp.is_Ok() && latest_cm.is_Ok() && latest_cm.get_Ok_0().metadata.resource_version.is_Some() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_service_account_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetServiceAccount,
                    latest_config_map_rv_opt: Some(int_to_string_view(latest_cm.get_Ok_0().metadata.resource_version.get_Some_0())),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdateServerConfigMap => {
            let update_cm_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_cm = ConfigMapView::unmarshal(update_cm_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_cm_resp.is_Ok() && latest_cm.is_Ok() && latest_cm.get_Ok_0().metadata.resource_version.is_Some() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_service_account_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetServiceAccount,
                    latest_config_map_rv_opt: Some(int_to_string_view(latest_cm.get_Ok_0().metadata.resource_version.get_Some_0())),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterGetServiceAccount => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let made_obj = make_service_account(rabbitmq);
                let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_resp.is_Ok() {
                    // update
                    if ServiceAccountView::unmarshal(get_resp.get_Ok_0()).is_Ok()
                    {
                        let found_obj = ServiceAccountView::unmarshal(get_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            name: make_service_account_name(rabbitmq),
                            obj: update_service_account(rabbitmq, found_obj).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateServiceAccount,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: made_obj.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateServiceAccount,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateServiceAccount => {
            let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_obj = ServiceAccountView::unmarshal(create_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_role_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetRole,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdateServiceAccount => {
            let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_obj = ServiceAccountView::unmarshal(update_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_role_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetRole,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterGetRole => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let made_obj = make_role(rabbitmq);
                let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_resp.is_Ok() {
                    // update
                    if RoleView::unmarshal(get_resp.get_Ok_0()).is_Ok()
                    {
                        let found_obj = RoleView::unmarshal(get_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            name: make_role_name(rabbitmq),
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            obj: update_role(rabbitmq, found_obj).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateRole,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: made_obj.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateRole,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateRole => {
            let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_obj = RoleView::unmarshal(create_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_role_binding_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetRoleBinding,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdateRole => {
            let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_obj = RoleView::unmarshal(update_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_role_binding_key(rabbitmq),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetRoleBinding,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterGetRoleBinding => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let made_obj = make_role_binding(rabbitmq);
                let get_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_resp.is_Ok() {
                    // update
                    if RoleBindingView::unmarshal(get_resp.get_Ok_0()).is_Ok()
                    {
                        let found_obj = RoleBindingView::unmarshal(get_resp.get_Ok_0()).get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            name: make_role_binding_name(rabbitmq),
                            namespace: rabbitmq.metadata.namespace.get_Some_0(),
                            obj: update_role_binding(rabbitmq, found_obj).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateRoleBinding,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: made_obj.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateRoleBinding,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateRoleBinding => {
            let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_obj = RoleBindingView::unmarshal(create_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_stateful_set_key(rabbitmq.object_ref()),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetStatefulSet,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdateRoleBinding => {
            let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_obj = RoleBindingView::unmarshal(update_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_resp.is_Ok() && latest_obj.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest{
                    key: make_stateful_set_key(rabbitmq.object_ref()),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetStatefulSet,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterGetStatefulSet => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_GetResponse()
            && state.latest_config_map_rv_opt.is_Some() {
                let get_sts_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_sts_resp.is_Ok() {
                    // update
                    if StatefulSetView::unmarshal(get_sts_resp.get_Ok_0()).is_Ok() {
                        let found_stateful_set = StatefulSetView::unmarshal(get_sts_resp.get_Ok_0()).get_Ok_0();
                        if found_stateful_set.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
                        && found_stateful_set.spec.is_Some() {
                            let req_o = APIRequest::UpdateRequest(UpdateRequest {
                                namespace: rabbitmq.metadata.namespace.get_Some_0(),
                                name: make_stateful_set_name(rabbitmq.metadata.name.get_Some_0()),
                                obj: update_stateful_set(
                                    rabbitmq, found_stateful_set,
                                    state.latest_config_map_rv_opt.get_Some_0()
                                ).marshal(),
                            });
                            let state_prime = RabbitmqReconcileState {
                                reconcile_step: RabbitmqReconcileStep::AfterUpdateStatefulSet,
                                ..state
                            };
                            (state_prime, Some(RequestView::KRequest(req_o)))
                        } else {
                            let state_prime = RabbitmqReconcileState {
                                reconcile_step: RabbitmqReconcileStep::Error,
                                ..state
                            };
                            (state_prime, None)
                        }
                    } else {
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_sts_resp.get_Err_0().is_ObjectNotFound() {
                    let stateful_set = make_stateful_set(rabbitmq, state.latest_config_map_rv_opt.get_Some_0());
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: rabbitmq.metadata.namespace.get_Some_0(),
                        obj: stateful_set.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateStatefulSet,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterCreateStatefulSet => {
            let create_resp = resp_o.get_Some_0().get_KResponse_0().get_CreateResponse_0().res;
            let latest_obj = StatefulSetView::unmarshal(create_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_CreateResponse()
            && create_resp.is_Ok() && latest_obj.is_Ok() {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        RabbitmqReconcileStep::AfterUpdateStatefulSet => {
            let update_resp = resp_o.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res;
            let latest_obj = StatefulSetView::unmarshal(update_resp.get_Ok_0());
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse() && resp_o.get_Some_0().get_KResponse_0().is_UpdateResponse()
            && update_resp.is_Ok() && latest_obj.is_Ok() {
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                // return error state
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        _ => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: step,
                ..state
            };
            (state_prime, None)
        }
    }
}

pub open spec fn reconcile_error_result(state: RabbitmqReconcileState) -> (RabbitmqReconcileState, Option<APIRequest>) {
    let state_prime = RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Error,
        ..state
    };
    let req_o = None;
    (state_prime, req_o)
}

}
