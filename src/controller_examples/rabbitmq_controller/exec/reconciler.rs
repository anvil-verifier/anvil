// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::resource::*;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::reconciler as rabbitmq_spec;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct RabbitmqReconciler {}

#[verifier(external)]
impl Reconciler<RabbitmqCluster, RabbitmqReconcileState, EmptyType, EmptyType, EmptyAPIShimLayer> for RabbitmqReconciler {
    fn reconcile_init_state(&self) -> RabbitmqReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, rabbitmq: &RabbitmqCluster, resp_o: Option<Response<EmptyType>>, state: RabbitmqReconcileState) -> (RabbitmqReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(rabbitmq, resp_o, state)
    }

    fn reconcile_done(&self, state: &RabbitmqReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(&self, state: &RabbitmqReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for RabbitmqReconciler {
    fn default() -> RabbitmqReconciler { RabbitmqReconciler{} }
}

pub fn reconcile_init_state() -> (state: RabbitmqReconcileState)
    ensures
        state@ == rabbitmq_spec::reconcile_init_state(),
{
    RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Init,
        latest_config_map_rv_opt: None,
    }
}

pub fn reconcile_done(state: &RabbitmqReconcileState) -> (res: bool)
    ensures
        res == rabbitmq_spec::reconcile_done(state@),
{
    match state.reconcile_step {
        RabbitmqReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &RabbitmqReconcileState) -> (res: bool)
    ensures
        res == rabbitmq_spec::reconcile_error(state@),
{
    match state.reconcile_step {
        RabbitmqReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(rabbitmq: &RabbitmqCluster, resp_o: Option<Response<EmptyType>>, state: RabbitmqReconcileState) -> (res: (RabbitmqReconcileState, Option<Request<EmptyType>>))
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        (res.0@, opt_request_to_view(&res.1)) == rabbitmq_spec::reconcile_core(rabbitmq@, opt_response_to_view(&resp_o), state@),
{
    let step = state.reconcile_step;
    match step{
        RabbitmqReconcileStep::Init => {
            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: Service::api_resource(),
                name: rabbitmq.name().unwrap().concat(new_strlit("-nodes")),
                namespace: rabbitmq.namespace().unwrap(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterGetHeadlessService,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterGetHeadlessService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let headless_service = make_headless_service(&rabbitmq);
                let get_service_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_service_resp.is_ok() {
                    // update
                    let found_headless_service = Service::unmarshal(get_service_resp.unwrap());
                    if found_headless_service.is_ok(){
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: Service::api_resource(),
                            name: headless_service.metadata().name().unwrap(),
                            namespace: rabbitmq.namespace().unwrap(),
                            obj: update_headless_service(rabbitmq, found_headless_service.unwrap()).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateHeadlessService,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_service_resp.unwrap_err().is_object_not_found() {
                    // create
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Service::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: headless_service.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateHeadlessService,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateHeadlessService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()
            && Service::unmarshal(resp_o.unwrap().into_k_response().into_create_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: Service::api_resource(),
                    name: rabbitmq.name().unwrap(),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetService,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterUpdateHeadlessService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()
            && Service::unmarshal(resp_o.unwrap().into_k_response().into_update_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: Service::api_resource(),
                    name: rabbitmq.name().unwrap(),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetService,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterGetService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let main_service = make_main_service(rabbitmq);
                let get_service_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_service_resp.is_ok() {
                    // update
                    let found_main_service = Service::unmarshal(get_service_resp.unwrap());
                    if found_main_service.is_ok(){
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: Service::api_resource(),
                            name: main_service.metadata().name().unwrap(),
                            namespace: rabbitmq.namespace().unwrap(),
                            obj: update_main_service(rabbitmq, found_main_service.unwrap()).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateService,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_service_resp.unwrap_err().is_object_not_found() {
                    // create
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Service::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: main_service.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateService,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()
            && Service::unmarshal(resp_o.unwrap().into_k_response().into_create_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: Secret::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-erlang-cookie")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetErlangCookieSecret,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterUpdateService => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()
            && Service::unmarshal(resp_o.unwrap().into_k_response().into_update_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: Secret::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-erlang-cookie")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetErlangCookieSecret,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterGetErlangCookieSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let erlang_secret = make_erlang_secret(rabbitmq);
                let get_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_resp.is_ok() {
                    // update
                    let found_erlang_secret = Secret::unmarshal(get_resp.unwrap());
                    if found_erlang_secret.is_ok(){
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: Secret::api_resource(),
                            name: erlang_secret.metadata().name().unwrap(),
                            namespace: rabbitmq.namespace().unwrap(),
                            obj: update_erlang_secret(rabbitmq, found_erlang_secret.unwrap()).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateErlangCookieSecret,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_resp.unwrap_err().is_object_not_found() {
                    // create
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Secret::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: erlang_secret.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateErlangCookieSecret,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateErlangCookieSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()
            && Secret::unmarshal(resp_o.unwrap().into_k_response().into_create_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: Secret::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-default-user")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetDefaultUserSecret,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterUpdateErlangCookieSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()
            && Secret::unmarshal(resp_o.unwrap().into_k_response().into_update_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: Secret::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-default-user")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetDefaultUserSecret,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterGetDefaultUserSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let default_user_secret = make_default_user_secret(rabbitmq);
                let get_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_resp.is_ok() {
                    // update
                    let found_user_secret = Secret::unmarshal(get_resp.unwrap());
                    if found_user_secret.is_ok(){
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: Secret::api_resource(),
                            name: default_user_secret.metadata().name().unwrap(),
                            namespace: rabbitmq.namespace().unwrap(),
                            obj: update_default_user_secret(rabbitmq, found_user_secret.unwrap()).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateDefaultUserSecret,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_resp.unwrap_err().is_object_not_found() {
                    // create
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Secret::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: default_user_secret.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateDefaultUserSecret,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateDefaultUserSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()
            && Secret::unmarshal(resp_o.unwrap().into_k_response().into_create_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: ConfigMap::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-plugins-conf")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetPluginsConfigMap,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterUpdateDefaultUserSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()
            && Secret::unmarshal(resp_o.unwrap().into_k_response().into_update_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: ConfigMap::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-plugins-conf")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetPluginsConfigMap,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterGetPluginsConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let plugins_config_map = make_plugins_config_map(rabbitmq);
                let get_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_resp.is_ok() {
                    // update
                    let found_config_map = ConfigMap::unmarshal(get_resp.unwrap());
                    if found_config_map.is_ok(){
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: ConfigMap::api_resource(),
                            name: plugins_config_map.metadata().name().unwrap(),
                            namespace: rabbitmq.namespace().unwrap(),
                            obj: update_plugins_config_map(rabbitmq, found_config_map.unwrap()).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdatePluginsConfigMap,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_resp.unwrap_err().is_object_not_found() {
                    // create
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: ConfigMap::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: plugins_config_map.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreatePluginsConfigMap,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreatePluginsConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()
            && ConfigMap::unmarshal(resp_o.unwrap().into_k_response().into_create_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: ConfigMap::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-server-conf")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetServerConfigMap,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterUpdatePluginsConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()
            && ConfigMap::unmarshal(resp_o.unwrap().into_k_response().into_update_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: ConfigMap::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-server-conf")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetServerConfigMap,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterGetServerConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let config_map = make_server_config_map(rabbitmq);
                let get_config_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_config_resp.is_ok() {
                    // update
                    let found_config_map = ConfigMap::unmarshal(get_config_resp.unwrap());
                    if found_config_map.is_ok(){
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: ConfigMap::api_resource(),
                            name: config_map.metadata().name().unwrap(),
                            namespace: rabbitmq.namespace().unwrap(),
                            obj: update_server_config_map(rabbitmq, found_config_map.unwrap()).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateServerConfigMap,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_config_resp.unwrap_err().is_object_not_found() {
                    // create
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: ConfigMap::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: config_map.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateServerConfigMap,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateServerConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok() {
                let create_config_resp = resp_o.unwrap().into_k_response().into_create_response().res;
                let created_config_map = ConfigMap::unmarshal(create_config_resp.unwrap());
                if created_config_map.is_ok() && created_config_map.as_ref().unwrap().metadata().resource_version().is_some() {
                    let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                        api_resource: ServiceAccount::api_resource(),
                        name: rabbitmq.name().unwrap().concat(new_strlit("-server")),
                        namespace: rabbitmq.namespace().unwrap(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterGetServiceAccount,
                        latest_config_map_rv_opt: created_config_map.unwrap().metadata().resource_version(),
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterUpdateServerConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok() {
                let update_config_resp = resp_o.unwrap().into_k_response().into_update_response().res;
                let updated_config_map = ConfigMap::unmarshal(update_config_resp.unwrap());
                if updated_config_map.is_ok() && updated_config_map.as_ref().unwrap().metadata().resource_version().is_some() {
                    let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                        api_resource: ServiceAccount::api_resource(),
                        name: rabbitmq.name().unwrap().concat(new_strlit("-server")),
                        namespace: rabbitmq.namespace().unwrap(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterGetServiceAccount,
                        latest_config_map_rv_opt: updated_config_map.unwrap().metadata().resource_version(),
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterGetServiceAccount => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let service_account = make_service_account(rabbitmq);
                let get_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_resp.is_ok() {
                    // update
                    let found_service_account = ServiceAccount::unmarshal(get_resp.unwrap());
                    if found_service_account.is_ok(){
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: ServiceAccount::api_resource(),
                            name: service_account.metadata().name().unwrap(),
                            namespace: rabbitmq.namespace().unwrap(),
                            obj: update_service_account(rabbitmq, found_service_account.unwrap()).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateServiceAccount,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_resp.unwrap_err().is_object_not_found() {
                    // create
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: ServiceAccount::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: service_account.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateServiceAccount,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateServiceAccount => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()
            && ServiceAccount::unmarshal(resp_o.unwrap().into_k_response().into_create_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: Role::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-peer-discovery")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetRole,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterUpdateServiceAccount => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()
            && ServiceAccount::unmarshal(resp_o.unwrap().into_k_response().into_update_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: Role::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-peer-discovery")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetRole,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterGetRole => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let role = make_role(rabbitmq);
                let get_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_resp.is_ok() {
                    // update
                    let found_role = Role::unmarshal(get_resp.unwrap());
                    if found_role.is_ok(){
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: Role::api_resource(),
                            name: role.metadata().name().unwrap(),
                            namespace: rabbitmq.namespace().unwrap(),
                            obj: update_role(rabbitmq, found_role.unwrap()).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateRole,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_resp.unwrap_err().is_object_not_found() {
                    // create
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Role::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: role.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateRole,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateRole => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()
            && Role::unmarshal(resp_o.unwrap().into_k_response().into_create_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: RoleBinding::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-server")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetRoleBinding,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterUpdateRole => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()
            && Role::unmarshal(resp_o.unwrap().into_k_response().into_update_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: RoleBinding::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-server")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetRoleBinding,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterGetRoleBinding => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let role_binding = make_role_binding(rabbitmq);
                let get_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_resp.is_ok() {
                    // update
                    let found_role_binding = RoleBinding::unmarshal(get_resp.unwrap());
                    if found_role_binding.is_ok(){
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: RoleBinding::api_resource(),
                            name: role_binding.metadata().name().unwrap(),
                            namespace: rabbitmq.namespace().unwrap(),
                            obj: update_role_binding(rabbitmq, found_role_binding.unwrap()).marshal(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateRoleBinding,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_resp.unwrap_err().is_object_not_found() {
                    // create
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: RoleBinding::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: role_binding.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateRoleBinding,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateRoleBinding => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()
            && RoleBinding::unmarshal(resp_o.unwrap().into_k_response().into_create_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: StatefulSet::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-server")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetStatefulSet,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterUpdateRoleBinding => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()
            && RoleBinding::unmarshal(resp_o.unwrap().into_k_response().into_update_response().res.unwrap()).is_ok() {
                let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: StatefulSet::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-server")),
                    namespace: rabbitmq.namespace().unwrap(),
                });
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::AfterGetStatefulSet,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            }
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterGetStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() && state.latest_config_map_rv_opt.is_some() {
                let get_sts_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_sts_resp.is_ok() {
                    // update
                    let get_sts_result = StatefulSet::unmarshal(get_sts_resp.unwrap());
                    if get_sts_result.is_ok(){
                        let mut found_stateful_set = get_sts_result.unwrap();
                        // We check the owner reference of the found stateful set here to ensure that it is not created from
                        // previously existing (and now deleted) cr. Otherwise, if the replicas of the current cr is smaller
                        // than the previous one, scaling down, which should be prohibited, will happen.
                        // If the found stateful set doesn't contain the controller owner reference of the current cr, we will
                        // just let the reconciler enter the error state and wait for the garbage collector to delete it. So
                        // after that, when a new round of reconcile starts, there is no stateful set in etcd, the reconciler
                        // will go to create a new one.
                        if found_stateful_set.metadata().owner_references_only_contains(rabbitmq.controller_owner_ref())
                        && found_stateful_set.spec().is_some() {
                            let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                                api_resource: StatefulSet::api_resource(),
                                name: make_stateful_set_name(rabbitmq),
                                namespace: rabbitmq.namespace().unwrap(),
                                obj: update_stateful_set(rabbitmq, found_stateful_set, state.latest_config_map_rv_opt.as_ref().unwrap()).marshal(),
                            });
                            let state_prime = RabbitmqReconcileState {
                                reconcile_step: RabbitmqReconcileStep::AfterUpdateStatefulSet,
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req_o)));
                        }
                    }
                } else if get_sts_resp.unwrap_err().is_object_not_found() {
                    // create
                    let stateful_set = make_stateful_set(rabbitmq, state.latest_config_map_rv_opt.as_ref().unwrap());
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: StatefulSet::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: stateful_set.marshal(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateStatefulSet,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }

            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()
            && StatefulSet::unmarshal(resp_o.unwrap().into_k_response().into_create_response().res.unwrap()).is_ok() {
                let req_o = None;
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Done,
                    ..state
                };
                return (state_prime, req_o);
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterUpdateStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()
            && StatefulSet::unmarshal(resp_o.unwrap().into_k_response().into_update_response().res.unwrap()).is_ok() {
                let req_o = None;
                let state_prime = RabbitmqReconcileState {
                    reconcile_step: RabbitmqReconcileStep::Done,
                    ..state
                };
                return (state_prime, req_o);
            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        },
        _ => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = None;
            return (state_prime, req_o);
        }
    }
}

}
