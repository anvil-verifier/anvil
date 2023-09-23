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
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct RabbitmqReconcileState {
    pub reconcile_step: RabbitmqReconcileStep,
    pub latest_config_map_rv_opt: Option<StringView>,
}

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

pub open spec fn make_labels(rabbitmq: RabbitmqClusterView) -> Map<StringView, StringView>
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.spec.labels.insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0())
}

pub open spec fn make_owner_references(rabbitmq: RabbitmqClusterView) -> Seq<OwnerReferenceView> {
    seq![rabbitmq.controller_owner_ref()]
}

pub open spec fn make_headless_service_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-nodes")@
}

pub open spec fn make_headless_service_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_headless_service_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_headless_service(rabbitmq: RabbitmqClusterView, found_headless_service: ServiceView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_service = make_headless_service(rabbitmq);
    ServiceView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_service.metadata.labels,
            annotations: made_service.metadata.annotations,
            ..found_headless_service.metadata
        },
        spec: made_service.spec,
        ..found_headless_service
    }
}

pub open spec fn make_headless_service(rabbitmq: RabbitmqClusterView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let mut ports = seq![
        ServicePortView::default().set_name(new_strlit("epmd")@).set_port(4369),
        ServicePortView::default().set_name(new_strlit("cluster-rpc")@).set_port(25672)
    ];
    make_service(rabbitmq, make_headless_service_name(rabbitmq), ports, false)
}

pub open spec fn make_main_service_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0()
}

pub open spec fn make_main_service_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_main_service_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_main_service(rabbitmq: RabbitmqClusterView, found_main_service: ServiceView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_main_service = make_main_service(rabbitmq);
    ServiceView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_main_service.metadata.labels,
            annotations: made_main_service.metadata.annotations,
            ..found_main_service.metadata
        },
        ..found_main_service
    }
}

pub open spec fn make_main_service(rabbitmq: RabbitmqClusterView) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let ports = seq![
        ServicePortView::default().set_name(new_strlit("amqp")@).set_port(5672).set_app_protocol(new_strlit("amqp")@),
        ServicePortView::default().set_name(new_strlit("management")@).set_port(15672).set_app_protocol(new_strlit("http")@),
        ServicePortView::default().set_name(new_strlit("prometheus")@).set_port(15692).set_app_protocol(new_strlit("prometheus.io/metrics")@),
    ];
    make_service(rabbitmq, make_main_service_name(rabbitmq), ports, true)
}

pub open spec fn make_service(
    rabbitmq: RabbitmqClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool
) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ServiceView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(name)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        ).set_spec({
            let spec = ServiceSpecView::default()
                .set_ports(ports)
                .set_selector(Map::empty()
                    .insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0())
                ).set_publish_not_ready_addresses(true);
            if !cluster_ip {
                spec.set_cluster_ip(new_strlit("None")@)
            } else {
                spec
            }
        })
}

pub open spec fn make_erlang_secret_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-erlang-cookie")@
}

pub open spec fn make_erlang_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: SecretView::kind(),
        name: make_erlang_secret_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_erlang_secret(rabbitmq: RabbitmqClusterView, found_erlang_secret: SecretView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_erlang_secret = make_erlang_secret(rabbitmq);
    SecretView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_erlang_secret.metadata.labels,
            annotations: made_erlang_secret.metadata.annotations,
            ..found_erlang_secret.metadata
        },
        ..found_erlang_secret
    }
}

pub open spec fn make_erlang_secret(rabbitmq: RabbitmqClusterView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let cookie = random_encoded_string(24);
    let data = Map::empty()
        .insert(new_strlit(".erlang.cookie")@, cookie);
    make_secret(rabbitmq, make_erlang_secret_name(rabbitmq), data)
}

pub closed spec fn random_encoded_string(length: usize) -> StringView;

pub open spec fn make_default_user_secret_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-default-user")@
}

pub open spec fn make_default_user_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: SecretView::kind(),
        name: make_default_user_secret_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_default_user_secret(rabbitmq: RabbitmqClusterView, found_secret: SecretView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_secret = make_default_user_secret(rabbitmq);
    SecretView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_secret.metadata.labels,
            annotations: made_secret.metadata.annotations,
            ..found_secret.metadata
        },
        ..found_secret
    }
}

pub open spec fn make_default_user_secret(rabbitmq: RabbitmqClusterView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let data = Map::empty()
        .insert(new_strlit("username")@, new_strlit("user")@)
        .insert(new_strlit("password")@, new_strlit("changeme")@)
        .insert(new_strlit("type")@, new_strlit("rabbitmq")@)
        .insert(new_strlit("host")@,
            rabbitmq.metadata.name.get_Some_0() + new_strlit(".")@ + rabbitmq.metadata.namespace.get_Some_0() + new_strlit(".svc")@,
        )
        .insert(new_strlit("provider")@, new_strlit("rabbitmq")@)
        .insert(new_strlit("default_user.conf")@, new_strlit("default_user = user\ndefault_pass = changeme")@)
        .insert(new_strlit("port")@, new_strlit("5672")@);
    make_secret(rabbitmq, make_default_user_secret_name(rabbitmq), data)
}

pub open spec fn make_secret(
    rabbitmq: RabbitmqClusterView, name: StringView, data: Map<StringView, StringView>
) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    SecretView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(name)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        ).set_data(data)
}

pub open spec fn make_plugins_config_map_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-plugins-conf")@
}

pub open spec fn make_plugins_config_map_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: ConfigMapView::kind(),
        name: make_plugins_config_map_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_plugins_config_map(rabbitmq: RabbitmqClusterView, found_config_map: ConfigMapView) -> ConfigMapView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_config_map = make_plugins_config_map(rabbitmq);
    ConfigMapView {
        data: Some({
            if found_config_map.data.is_Some() {
                found_config_map.data.get_Some_0()
                    .insert(new_strlit("enabled_plugins")@, new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].")@)
            } else {
                Map::empty().insert(
                    new_strlit("enabled_plugins")@,
                    new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].")@
                )
            }
        }),
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_config_map.metadata.labels,
            annotations: made_config_map.metadata.annotations,
            ..found_config_map.metadata
        },
        ..found_config_map
    }
}

pub open spec fn make_plugins_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ConfigMapView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_plugins_config_map_name(rabbitmq))
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        )
        .set_data(Map::empty()
            .insert(new_strlit("enabled_plugins")@, new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].")@)
        )
}

pub open spec fn update_server_config_map(rabbitmq: RabbitmqClusterView, found_config_map: ConfigMapView) -> ConfigMapView {
    ConfigMapView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: make_server_config_map(rabbitmq).metadata.labels,
            annotations: make_server_config_map(rabbitmq).metadata.annotations,
            ..found_config_map.metadata
        },
        data: Some({
            let old_data = if found_config_map.data.is_Some() { found_config_map.data.get_Some_0() } else { Map::empty() };
            old_data.union_prefer_right(make_server_config_map(rabbitmq).data.get_Some_0())
        }),
        ..found_config_map
    }
}

pub open spec fn make_server_config_map_name(rabbitmq_name: StringView) -> StringView {
    rabbitmq_name + new_strlit("-server-conf")@
}

pub open spec fn make_server_config_map_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: ConfigMapView::kind(),
        name: make_server_config_map_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn make_server_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ConfigMapView {
        metadata: ObjectMetaView {
            name: Some(make_server_config_map_name(rabbitmq.metadata.name.get_Some_0())),
            namespace: rabbitmq.metadata.namespace,
            owner_references: Some(make_owner_references(rabbitmq)),
            labels: Some(make_labels(rabbitmq)),
            annotations: Some(rabbitmq.spec.annotations),
            ..ObjectMetaView::default()
        },
        data: Some({
            let data = Map::empty()
                        .insert(new_strlit("operatorDefaults.conf")@, default_rbmq_config(rabbitmq))
                        .insert(new_strlit("userDefinedConfiguration.conf")@,
                        {
                            if rabbitmq.spec.rabbitmq_config.is_Some()
                            && rabbitmq.spec.rabbitmq_config.get_Some_0().additional_config.is_Some()
                            {   // check if there are rabbitmq-related customized configurations
                                new_strlit("total_memory_available_override_value = 1717986919\n")@ + rabbitmq.spec.rabbitmq_config.get_Some_0().additional_config.get_Some_0()
                            } else {
                                new_strlit("total_memory_available_override_value = 1717986919\n")@
                            }
                        });
            if rabbitmq.spec.rabbitmq_config.is_Some() && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.is_Some()
            && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.get_Some_0() != new_strlit("")@
            && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.is_Some()
            && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.get_Some_0() != new_strlit("")@ {
                data.insert(new_strlit("advanced.config")@, rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.get_Some_0())
                    .insert(new_strlit("rabbitmq-env.conf")@, rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.get_Some_0())
            } else if rabbitmq.spec.rabbitmq_config.is_Some() && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.is_Some()
            && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.get_Some_0() != new_strlit("")@ {
                data.insert(new_strlit("advanced.config")@, rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.get_Some_0())
            } else if rabbitmq.spec.rabbitmq_config.is_Some() && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.is_Some()
            && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.get_Some_0() != new_strlit("")@ {
                data.insert(new_strlit("rabbitmq-env.conf")@, rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.get_Some_0())
            } else {
                data
            }
        }),
        ..ConfigMapView::default()
    }
}

pub open spec fn default_rbmq_config(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let name = rabbitmq.metadata.name.get_Some_0();

    new_strlit(
        "queue_master_locator = min-masters\n\
        disk_free_limit.absolute = 2GB\n\
        cluster_partition_handling = pause_minority\n\
        cluster_formation.peer_discovery_backend = rabbit_peer_discovery_k8s\n\
        cluster_formation.k8s.host = kubernetes.default\n\
        cluster_formation.k8s.address_type = hostname\n"
    )@ + new_strlit("cluster_formation.target_cluster_size_hint = ")@ + int_to_string_view(rabbitmq.spec.replicas) + new_strlit("\n")@
    + new_strlit("cluster_name = ")@ + name + new_strlit("\n")@
}

pub open spec fn make_service_account_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@
}

pub open spec fn make_service_account_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: ServiceAccountView::kind(),
        name: make_service_account_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_service_account(rabbitmq: RabbitmqClusterView, found_service_account: ServiceAccountView) -> ServiceAccountView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_service_account = make_service_account(rabbitmq);
    ServiceAccountView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_service_account.metadata.labels,
            annotations: made_service_account.metadata.annotations,
            ..found_service_account.metadata
        },
        ..found_service_account
    }
}

pub open spec fn make_service_account(rabbitmq: RabbitmqClusterView) -> ServiceAccountView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ServiceAccountView {
        metadata: ObjectMetaView {
            name: Some(make_service_account_name(rabbitmq)),
            namespace: rabbitmq.metadata.namespace,
            owner_references: Some(make_owner_references(rabbitmq)),
            labels: Some(make_labels(rabbitmq)),
            annotations: Some(rabbitmq.spec.annotations),
            ..ObjectMetaView::default()
        },
        ..ServiceAccountView::default()
    }
}

pub open spec fn make_role_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-peer-discovery")@
}

pub open spec fn make_role_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: RoleView::kind(),
        name: make_role_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_role(rabbitmq: RabbitmqClusterView, found_role: RoleView) -> RoleView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_role = make_role(rabbitmq);
    RoleView {
        policy_rules: made_role.policy_rules,
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_role.metadata.labels,
            annotations: made_role.metadata.annotations,
            ..found_role.metadata
        },
        ..found_role
    }
}

pub open spec fn make_role(rabbitmq: RabbitmqClusterView) -> RoleView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    RoleView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_role_name(rabbitmq))
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        ).set_policy_rules(
            seq![
                PolicyRuleView::default().set_api_groups(seq![new_strlit("")@]).set_resources(seq![new_strlit("endpoints")@]).set_verbs(seq![new_strlit("get")@]),
                PolicyRuleView::default().set_api_groups(seq![new_strlit("")@]).set_resources(seq![new_strlit("events")@]).set_verbs(seq![new_strlit("create")@]),
            ]
        )
}

pub open spec fn make_role_binding_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@
}

pub open spec fn make_role_binding_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: RoleBindingView::kind(),
        name: make_role_binding_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_role_binding(rabbitmq: RabbitmqClusterView, found_role_binding: RoleBindingView) -> RoleBindingView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_role_binding = make_role_binding(rabbitmq);
    RoleBindingView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_role_binding.metadata.labels,
            annotations: made_role_binding.metadata.annotations,
            ..found_role_binding.metadata
        },
        role_ref: made_role_binding.role_ref,
        subjects: made_role_binding.subjects,
        ..found_role_binding
    }
}

pub open spec fn make_role_binding(rabbitmq: RabbitmqClusterView) -> RoleBindingView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    RoleBindingView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_role_binding_name(rabbitmq))
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        ).set_role_ref(RoleRefView::default()
            .set_api_group(new_strlit("rbac.authorization.k8s.io")@)
            .set_kind(new_strlit("Role")@)
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-peer-discovery")@)
        ).set_subjects(seq![SubjectView::default()
            .set_kind(new_strlit("ServiceAccount")@)
            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
        ])
}

pub open spec fn make_stateful_set_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: StatefulSetView::kind(),
        name: make_stateful_set_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn make_stateful_set_name(rabbitmq_name: StringView) -> StringView {
    rabbitmq_name + new_strlit("-server")@
}

pub open spec fn update_stateful_set(
    rabbitmq: RabbitmqClusterView, found_stateful_set: StatefulSetView, config_map_rv: StringView
) -> StatefulSetView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
        found_stateful_set.spec.is_Some(),
{
    let made_spec = make_stateful_set(rabbitmq, config_map_rv).spec.get_Some_0();
    StatefulSetView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: make_stateful_set(rabbitmq, config_map_rv).metadata.labels,
            annotations: make_stateful_set(rabbitmq, config_map_rv).metadata.annotations,
            ..found_stateful_set.metadata
        },
        spec: Some(StatefulSetSpecView {
            replicas: made_spec.replicas,
            template: made_spec.template,
            persistent_volume_claim_retention_policy: made_spec.persistent_volume_claim_retention_policy,
            ..found_stateful_set.spec.get_Some_0()
        }),
        ..found_stateful_set
    }
}

pub open spec fn sts_restart_annotation() -> StringView {
    new_strlit("anvil.dev/lastRestartAt")@
}

pub open spec fn make_stateful_set(rabbitmq: RabbitmqClusterView, config_map_rv: StringView) -> StatefulSetView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let name = rabbitmq.metadata.name.get_Some_0();
    let sts_name = make_stateful_set_name(name);
    let namespace = rabbitmq.metadata.namespace.get_Some_0();

    let labels = Map::empty().insert(new_strlit("app")@, name);
    let metadata = ObjectMetaView::default()
        .set_name(sts_name)
        .set_namespace(namespace)
        .set_owner_references(make_owner_references(rabbitmq))
        .set_labels(make_labels(rabbitmq))
        .set_annotations(rabbitmq.spec.annotations);

    let spec = StatefulSetSpecView {
        replicas: Some(rabbitmq.spec.replicas),
        service_name: name + new_strlit("-nodes")@,
        selector: LabelSelectorView::default().set_match_labels(labels),
        template: PodTemplateSpecView::default()
                    .set_metadata(
                        ObjectMetaView::default().set_labels(
                            make_labels(rabbitmq)
                        ).set_annotations(
                            rabbitmq.spec.annotations.insert(sts_restart_annotation(), config_map_rv)
                        )
                    )
                    .set_spec(make_rabbitmq_pod_spec(rabbitmq)),
        volume_claim_templates: Some({
            if rabbitmq.spec.persistence.storage == new_strlit("0Gi")@ {
                seq![]
            } else {
                seq![
                    PersistentVolumeClaimView::default()
                        .set_metadata(ObjectMetaView::default()
                            .set_name(new_strlit("persistence")@)
                            .set_namespace(namespace)
                            .set_labels(labels)
                        )
                        .set_spec(PersistentVolumeClaimSpecView::default()
                            .set_access_modes(seq![new_strlit("ReadWriteOnce")@])
                            .set_resources(ResourceRequirementsView::default()
                                .set_requests(Map::empty()
                                    .insert(new_strlit("storage")@, rabbitmq.spec.persistence.storage)
                                )
                            )
                            .overwrite_storage_class_name(rabbitmq.spec.persistence.storage_class_name)
                        )
                ]
            }
        }),
        pod_management_policy: Some({
            if rabbitmq.spec.pod_management_policy.is_Some() {
                rabbitmq.spec.pod_management_policy.get_Some_0()
            } else {
                new_strlit("Parallel")@
            }
        }),
        persistent_volume_claim_retention_policy: rabbitmq.spec.persistent_volume_claim_retention_policy,
        ..StatefulSetSpecView::default()

    };

    StatefulSetView::default().set_metadata(metadata).set_spec(spec)
}

pub open spec fn make_rabbitmq_pod_spec(rabbitmq: RabbitmqClusterView) -> PodSpecView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let volumes = seq![
        VolumeView::default()
            .set_name(new_strlit("plugins-conf")@)
            .set_config_map(ConfigMapVolumeSourceView::default()
                .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-plugins-conf")@)
            ),
        VolumeView::default()
            .set_name(new_strlit("rabbitmq-confd")@)
            .set_projected(ProjectedVolumeSourceView::default()
                .set_sources(seq![
                    VolumeProjectionView::default()
                        .set_config_map(ConfigMapProjectionView::default()
                            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server-conf")@)
                            .set_items(seq![
                                KeyToPathView::default()
                                    .set_key(new_strlit("operatorDefaults.conf")@)
                                    .set_path(new_strlit("operatorDefaults.conf")@),
                                KeyToPathView::default()
                                    .set_key(new_strlit("userDefinedConfiguration.conf")@)
                                    .set_path(new_strlit("userDefinedConfiguration.conf")@),
                            ])
                        ),
                    VolumeProjectionView::default()
                        .set_secret(SecretProjectionView::default()
                            .set_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-default-user")@)
                            .set_items(seq![
                                KeyToPathView::default()
                                    .set_key(new_strlit("default_user.conf")@)
                                    .set_path(new_strlit("default_user.conf")@),
                            ])
                        ),
                ])
            ),
        VolumeView::default()
            .set_name(new_strlit("rabbitmq-erlang-cookie")@)
            .set_empty_dir(EmptyDirVolumeSourceView::default()),
        VolumeView::default()
            .set_name(new_strlit("erlang-cookie-secret")@)
            .set_secret(SecretVolumeSourceView::default()
                .set_secret_name(rabbitmq.metadata.name.get_Some_0() + new_strlit("-erlang-cookie")@)
            ),
        VolumeView::default()
            .set_name(new_strlit("rabbitmq-plugins")@)
            .set_empty_dir(EmptyDirVolumeSourceView::default()),
        VolumeView::default()
            .set_name(new_strlit("pod-info")@)
            .set_downward_api(DownwardAPIVolumeSourceView::default()
                .set_items(seq![
                    DownwardAPIVolumeFileView::default()
                        .set_path(new_strlit("skipPreStopChecks")@)
                        .set_field_ref(ObjectFieldSelectorView::default()
                            .set_field_path(new_strlit("metadata.labels['skipPreStopChecks']")@)
                        ),
                ])
            ),
    ];

    PodSpecView {
        service_account_name: Some(rabbitmq.metadata.name.get_Some_0() + new_strlit("-server")@),
        init_containers: Some(
            seq![
                ContainerView::default()
                .set_name(new_strlit("setup-container")@)
                .set_image(rabbitmq.spec.image)
                .set_command(
                    seq![
                        new_strlit("sh")@,
                        new_strlit("-c")@,
                        new_strlit("cp /tmp/erlang-cookie-secret/.erlang.cookie /var/lib/rabbitmq/.erlang.cookie && chmod 600 /var/lib/rabbitmq/.erlang.cookie ; cp /tmp/rabbitmq-plugins/enabled_plugins /operator/enabled_plugins ; echo '[default]' > /var/lib/rabbitmq/.rabbitmqadmin.conf && sed -e 's/default_user/username/' -e 's/default_pass/password/' /tmp/default_user.conf >> /var/lib/rabbitmq/.rabbitmqadmin.conf && chmod 600 /var/lib/rabbitmq/.rabbitmqadmin.conf ; sleep 30")@
                    ]
                )
                .set_resources(
                    ResourceRequirementsView {
                        limits: Some(Map::empty().insert(new_strlit("cpu")@, new_strlit("100m")@).insert(new_strlit("memory")@, new_strlit("500Mi")@)),
                        requests: Some(Map::empty().insert(new_strlit("cpu")@, new_strlit("100m")@).insert(new_strlit("memory")@, new_strlit("500Mi")@)),
                    }
                )
                .set_volume_mounts(seq![
                    VolumeMountView::default()
                        .set_name(new_strlit("plugins-conf")@)
                        .set_mount_path(new_strlit("/tmp/rabbitmq-plugins/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-erlang-cookie")@)
                        .set_mount_path(new_strlit("/var/lib/rabbitmq/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("erlang-cookie-secret")@)
                        .set_mount_path(new_strlit("/tmp/erlang-cookie-secret/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-plugins")@)
                        .set_mount_path(new_strlit("/operator")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("persistence")@)
                        .set_mount_path(new_strlit("/var/lib/rabbitmq/mnesia/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-confd")@)
                        .set_mount_path(new_strlit("/etc/pod-info/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-confd")@)
                        .set_mount_path(new_strlit("/tmp/default_user.conf")@)
                        .set_sub_path(new_strlit("default_user.conf")@),
                ])
            ]
        ),
        containers: seq![
            ContainerView {
                name: new_strlit("rabbitmq")@,
                image: Some(rabbitmq.spec.image),
                env: Some(make_env_vars(rabbitmq)),
                volume_mounts: Some(seq![
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-erlang-cookie")@)
                        .set_mount_path(new_strlit("/var/lib/rabbitmq/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("persistence")@)
                        .set_mount_path(new_strlit("/var/lib/rabbitmq/mnesia/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-plugins")@)
                        .set_mount_path(new_strlit("/operator")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-confd")@)
                        .set_mount_path(new_strlit("/etc/rabbitmq/conf.d/10-operatorDefaults.conf")@)
                        .set_sub_path(new_strlit("operatorDefaults.conf")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-confd")@)
                        .set_mount_path(new_strlit("/etc/rabbitmq/conf.d/90-userDefinedConfiguration.conf")@)
                        .set_sub_path(new_strlit("userDefinedConfiguration.conf")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("pod-info")@)
                        .set_mount_path(new_strlit("/etc/pod-info/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("rabbitmq-confd")@)
                        .set_mount_path(new_strlit("/etc/rabbitmq/conf.d/11-default_user.conf")@)
                        .set_sub_path(new_strlit("default_user.conf")@),
                ]),
                ports: Some(seq![
                    ContainerPortView::default().set_name(new_strlit("epmd")@).set_container_port(4369),
                    ContainerPortView::default().set_name(new_strlit("amqp")@).set_container_port(5672),
                    ContainerPortView::default().set_name(new_strlit("management")@).set_container_port(15672),
                ]),
                readiness_probe: Some(
                    ProbeView::default()
                        .set_failure_threshold(3)
                        .set_initial_delay_seconds(50)
                        .set_period_seconds(10)
                        .set_success_threshold(1)
                        .set_timeout_seconds(5)
                        .set_tcp_socket(TCPSocketActionView::default().set_port(5672))
                ),
                resources: rabbitmq.spec.resources,
                ..ContainerView::default()
            }
        ],
        volumes: Some({
            if rabbitmq.spec.persistence.storage == new_strlit("0Gi")@ {
                volumes.push(VolumeView::default().set_name(new_strlit("persistence")@).set_empty_dir(EmptyDirVolumeSourceView::default()))
            } else {
                volumes
            }
        }),
        affinity: rabbitmq.spec.affinity,
        tolerations: rabbitmq.spec.tolerations,
        ..PodSpecView::default()
    }
}

pub open spec fn make_env_vars(rabbitmq: RabbitmqClusterView) -> Seq<EnvVarView> {
    seq![
        EnvVarView {
            name: new_strlit("MY_POD_NAME")@,
            value_from: Some(EnvVarSourceView {
                field_ref: Some(ObjectFieldSelectorView{
                    api_version: Some(new_strlit("v1")@),
                    field_path: new_strlit("metadata.name")@,
                    ..ObjectFieldSelectorView::default()
                }),
                ..EnvVarSourceView::default()
            }),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("MY_POD_NAMESPACE")@,
            value_from: Some(EnvVarSourceView {
                field_ref: Some(ObjectFieldSelectorView{
                    api_version: Some(new_strlit("v1")@),
                    field_path: new_strlit("metadata.namespace")@,
                    ..ObjectFieldSelectorView::default()
                }),
                ..EnvVarSourceView::default()
            }),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("K8S_SERVICE_NAME")@,
            value: Some(rabbitmq.metadata.name.get_Some_0() + new_strlit("-nodes")@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("RABBITMQ_ENABLED_PLUGINS_FILE")@,
            value: Some(new_strlit("/operator/enabled_plugins")@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("RABBITMQ_USE_LONGNAME")@,
            value: Some(new_strlit("true")@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("RABBITMQ_NODENAME")@,
            value: Some(new_strlit("rabbit@$(MY_POD_NAME).$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)")@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("K8S_HOSTNAME_SUFFIX")@,
            value: Some(new_strlit(".$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)")@),
            ..EnvVarView::default()
        },
    ]
}

}
