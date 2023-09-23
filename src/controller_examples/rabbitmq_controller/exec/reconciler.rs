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
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::reconciler as rabbitmq_spec;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

/// RabbitmqReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct RabbitmqReconcileState {
    // reconcile_step, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_step: RabbitmqReconcileStep,
    pub latest_config_map_rv_opt: Option<String>,
}

impl RabbitmqReconcileState {
    pub open spec fn to_view(&self) -> rabbitmq_spec::RabbitmqReconcileState {
        rabbitmq_spec::RabbitmqReconcileState {
            reconcile_step: self.reconcile_step,
            latest_config_map_rv_opt: match &self.latest_config_map_rv_opt {
                Some(s) => Some(s@),
                None => None,
            },
        }
    }
}

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
        state.to_view() == rabbitmq_spec::reconcile_init_state(),
{
    RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Init,
        latest_config_map_rv_opt: None,
    }
}

pub fn reconcile_done(state: &RabbitmqReconcileState) -> (res: bool)
    ensures
        res == rabbitmq_spec::reconcile_done(state.to_view()),
{
    match state.reconcile_step {
        RabbitmqReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &RabbitmqReconcileState) -> (res: bool)
    ensures
        res == rabbitmq_spec::reconcile_error(state.to_view()),
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
        (res.0.to_view(), opt_request_to_view(&res.1)) == rabbitmq_spec::reconcile_core(rabbitmq@, opt_response_to_view(&resp_o), state.to_view()),
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

fn make_labels(rabbitmq: &RabbitmqCluster) -> (labels: StringMap)
    requires
        rabbitmq@.metadata.name.is_Some(),
    ensures
        labels@ == rabbitmq_spec::make_labels(rabbitmq@),
{
    let mut labels = rabbitmq.spec().labels();
    labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
    labels
}

fn make_owner_references(rabbitmq: &RabbitmqCluster) -> (owner_references: Vec<OwnerReference>)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        owner_references@.map_values(|or: OwnerReference| or@) ==  rabbitmq_spec::make_owner_references(rabbitmq@),
{
    let mut owner_references = Vec::new();
    owner_references.push(rabbitmq.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
            rabbitmq_spec::make_owner_references(rabbitmq@)
        );
    }
    owner_references
}

pub fn update_headless_service(rabbitmq: &RabbitmqCluster, found_headless_service: Service) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == rabbitmq_spec::update_headless_service(rabbitmq@, found_headless_service@),
{
    let made_service = make_headless_service(rabbitmq);

    let mut headless_service = found_headless_service.clone();
    headless_service.set_spec(made_service.spec().unwrap());
    headless_service.set_metadata({
        let mut metadata = found_headless_service.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_service.metadata().labels().unwrap());
        metadata.set_annotations(made_service.metadata().annotations().unwrap());
        metadata
    });
    headless_service
}

pub fn make_headless_service(rabbitmq: &RabbitmqCluster) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == rabbitmq_spec::make_headless_service(rabbitmq@)
{
    let mut ports = Vec::new();
    ports.push(ServicePort::new_with(new_strlit("epmd").to_string(), 4369));
    ports.push(ServicePort::new_with(new_strlit("cluster-rpc").to_string(), 25672));
    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            rabbitmq_spec::make_headless_service(rabbitmq@).spec.get_Some_0().ports.get_Some_0()
        );
    }
    make_service(rabbitmq, rabbitmq.name().unwrap().concat(new_strlit("-nodes")), ports, false)
}

fn update_main_service(rabbitmq: &RabbitmqCluster, found_main_service: Service) -> (service: Service)
requires
    rabbitmq@.metadata.name.is_Some(),
    rabbitmq@.metadata.namespace.is_Some(),
ensures
    service@ == rabbitmq_spec::update_main_service(rabbitmq@, found_main_service@),
{
    let mut main_service = found_main_service.clone();
    let made_service = make_main_service(rabbitmq);
    // TODO: whether to update the ports
    main_service.set_metadata({
        let mut metadata = found_main_service.metadata();
        // The reason why we add these two operations is that it makes the proof easier.
        // In this way, we can easily show that what the owner references and finalizers of the object in every update request
        // for stateful set are.
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_service.metadata().labels().unwrap());
        metadata.set_annotations(made_service.metadata().annotations().unwrap());
        metadata
    });
    main_service
}

pub fn make_main_service(rabbitmq: &RabbitmqCluster) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == rabbitmq_spec::make_main_service(rabbitmq@)
{
    let mut ports = Vec::new();
    // TODO: check whether the protocols are set to TCP
    ports.push({
        let mut port = ServicePort::new_with(new_strlit("amqp").to_string(), 5672);
        port.set_app_protocol(new_strlit("amqp").to_string());
        port
    });
    ports.push({
        let mut port = ServicePort::new_with(new_strlit("management").to_string(), 15672);
        port.set_app_protocol(new_strlit("http").to_string());
        port
    });
    ports.push({
        let mut port = ServicePort::new_with(new_strlit("prometheus").to_string(), 15692);
        port.set_app_protocol(new_strlit("prometheus.io/metrics").to_string());
        port
    });
    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            rabbitmq_spec::make_main_service(rabbitmq@).spec.get_Some_0().ports.get_Some_0()
        );
    }
    make_service(rabbitmq, rabbitmq.name().unwrap(), ports, true)
}

pub fn make_service(rabbitmq: &RabbitmqCluster, name:String, ports: Vec<ServicePort>, cluster_ip: bool) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == rabbitmq_spec::make_service(rabbitmq@, name@, ports@.map_values(|port: ServicePort| port@), cluster_ip)
{
    let mut service = Service::default();
    service.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(name);
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    service.set_spec({
        let mut service_spec = ServiceSpec::default();
        if !cluster_ip {
            service_spec.set_cluster_ip(new_strlit("None").to_string());
        }
        service_spec.set_ports(ports);
        service_spec.set_selector({
            let mut selector = StringMap::empty();
            selector.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            selector
        });
        service_spec.set_publish_not_ready_addresses(true);
        service_spec
    });
    service
}

fn update_erlang_secret(rabbitmq: &RabbitmqCluster, found_erlang_secret: Secret) -> (secret: Secret)
requires
    rabbitmq@.metadata.name.is_Some(),
    rabbitmq@.metadata.namespace.is_Some(),
ensures
    secret@ == rabbitmq_spec::update_erlang_secret(rabbitmq@, found_erlang_secret@),
{
    let mut erlang_secret = found_erlang_secret.clone();
    let made_secret = make_erlang_secret(rabbitmq);
    erlang_secret.set_metadata({
        let mut metadata = found_erlang_secret.metadata();
        let mut owner_references = Vec::new();
        owner_references.push(rabbitmq.controller_owner_ref());
        proof {
            assert_seqs_equal!(
                owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                rabbitmq_spec::update_erlang_secret(rabbitmq@, found_erlang_secret@).metadata.owner_references.get_Some_0()
            );
        }
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_secret.metadata().labels().unwrap());
        metadata.set_annotations(made_secret.metadata().annotations().unwrap());
        metadata
    });
    erlang_secret
}

fn make_erlang_secret(rabbitmq: &RabbitmqCluster) -> (secret: Secret)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        secret@ == rabbitmq_spec::make_erlang_secret(rabbitmq@)
{
    let mut data = StringMap::empty();
    let cookie = random_encoded_string(24);
    data.insert(new_strlit(".erlang.cookie").to_string(), cookie);
    make_secret(rabbitmq, rabbitmq.name().unwrap().concat(new_strlit("-erlang-cookie")), data)
}

#[verifier(external_body)]
fn random_encoded_string(data_len: usize) -> (cookie: String)
    ensures
        cookie@ == rabbitmq_spec::random_encoded_string(data_len),
{
    let random_bytes: std::vec::Vec<std::primitive::u8> = (0..data_len).map(|_| deps_hack::rand::random::<std::primitive::u8>()).collect();
    String::from_rust_string(deps_hack::base64::encode(random_bytes))
}

fn update_default_user_secret(rabbitmq: &RabbitmqCluster, found_secret: Secret) -> (secret: Secret)
requires
    rabbitmq@.metadata.name.is_Some(),
    rabbitmq@.metadata.namespace.is_Some(),
ensures
    secret@ == rabbitmq_spec::update_default_user_secret(rabbitmq@, found_secret@),
{
    let mut user_secret = found_secret.clone();
    let made_user_secret = make_default_user_secret(rabbitmq);
    // TODO: whether to update ports
    user_secret.set_metadata({
        let mut metadata = found_secret.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_user_secret.metadata().labels().unwrap());
        metadata.set_annotations(made_user_secret.metadata().annotations().unwrap());
        metadata
    });
    user_secret
}

fn make_default_user_secret(rabbitmq: &RabbitmqCluster) -> (secret: Secret)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        secret@ == rabbitmq_spec::make_default_user_secret(rabbitmq@)
{
    let mut data = StringMap::empty();
    data.insert(new_strlit("username").to_string(), new_strlit("user").to_string());
    data.insert(new_strlit("password").to_string(), new_strlit("changeme").to_string());
    data.insert(new_strlit("type").to_string(), new_strlit("rabbitmq").to_string());
    data.insert(new_strlit("host").to_string(),
            rabbitmq.name().unwrap().concat(new_strlit(".")).concat(rabbitmq.namespace().unwrap().as_str()).concat(new_strlit(".svc"))
    );
    data.insert(new_strlit("provider").to_string(), new_strlit("rabbitmq").to_string());
    // TODO: check \n
    data.insert(new_strlit("default_user.conf").to_string(), new_strlit("default_user = user\ndefault_pass = changeme").to_string());
    data.insert(new_strlit("port").to_string(), new_strlit("5672").to_string());
    make_secret(rabbitmq, rabbitmq.name().unwrap().concat(new_strlit("-default-user")), data)
}

pub fn make_secret(rabbitmq: &RabbitmqCluster, name:String , data: StringMap) -> (secret: Secret)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        secret@ == rabbitmq_spec::make_secret(rabbitmq@, name@, data@)
{
    let mut secret = Secret::default();
    secret.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(name);
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    secret.set_data(data);
    secret
}

fn update_plugins_config_map(rabbitmq: &RabbitmqCluster, found_config_map: ConfigMap) -> (config_map: ConfigMap)
requires
    rabbitmq@.metadata.name.is_Some(),
    rabbitmq@.metadata.namespace.is_Some(),
ensures
    config_map@ == rabbitmq_spec::update_plugins_config_map(rabbitmq@, found_config_map@),
{
    let mut config_map = found_config_map.clone();
    let made_config_map = make_plugins_config_map(rabbitmq);
    config_map.set_data({
        let mut data = if found_config_map.data().is_some() { found_config_map.data().unwrap() } else { StringMap::empty() };
        data.insert(new_strlit("enabled_plugins").to_string(),
                new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].").to_string());
        data
    });
    config_map.set_metadata({
        let mut metadata = found_config_map.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_config_map.metadata().labels().unwrap());
        metadata.set_annotations(made_config_map.metadata().annotations().unwrap());
        metadata
    });
    config_map
}

fn make_plugins_config_map(rabbitmq: &RabbitmqCluster) -> (config_map: ConfigMap)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        config_map@ == rabbitmq_spec::make_plugins_config_map(rabbitmq@),
{
    let mut config_map = ConfigMap::default();
    config_map.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(rabbitmq.name().unwrap().concat(new_strlit("-plugins-conf")));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    let mut data = StringMap::empty();
    data.insert(new_strlit("enabled_plugins").to_string(),
                new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].").to_string());
    config_map.set_data(data);
    config_map
}

fn update_server_config_map(rabbitmq: &RabbitmqCluster, found_config_map: ConfigMap) -> (config_map: ConfigMap)
requires
    rabbitmq@.metadata.name.is_Some(),
    rabbitmq@.metadata.namespace.is_Some(),
ensures
    config_map@ == rabbitmq_spec::update_server_config_map(rabbitmq@, found_config_map@),
{
    let mut config_map = found_config_map.clone();
    let made_server_cm = make_server_config_map(rabbitmq);

    config_map.set_data({
        let old_data_opt = found_config_map.data();
        let mut old_data = if old_data_opt.is_some() { old_data_opt.unwrap() } else { StringMap::empty() };
        old_data.extend(made_server_cm.data().unwrap());
        old_data
    });
    config_map.set_metadata({
        let mut metadata = found_config_map.metadata();
        // The reason why we add these two operations is that it makes the proof easier.
        // In this way, we can easily show that what the owner references and finalizers of the object in every update request
        // for stateful set are.
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_server_cm.metadata().labels().unwrap());
        metadata.set_annotations(made_server_cm.metadata().annotations().unwrap());
        metadata
    });
    config_map
}

fn make_server_config_map(rabbitmq: &RabbitmqCluster) -> (config_map: ConfigMap)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        config_map@ == rabbitmq_spec::make_server_config_map(rabbitmq@),
{
    let mut config_map = ConfigMap::default();
    config_map.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(rabbitmq.name().unwrap().concat(new_strlit("-server-conf")));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    let mut data = StringMap::empty();
    data.insert(new_strlit("operatorDefaults.conf").to_string(),
                default_rbmq_config(rabbitmq));
    data.insert(new_strlit("userDefinedConfiguration.conf").to_string(), {
        let mut rmq_conf_buff = new_strlit("total_memory_available_override_value = 1717986919\n").to_string(); // default value
        if rabbitmq.spec().rabbitmq_config().is_some() {
            // check if there are rabbitmq-related customized configurations
            let rabbitmq_config = rabbitmq.spec().rabbitmq_config().unwrap();
            if rabbitmq_config.additional_config().is_some(){
                rmq_conf_buff.append(rabbitmq_config.additional_config().unwrap().as_str());
            }
        }
        rmq_conf_buff
    });
    if rabbitmq.spec().rabbitmq_config().is_some() && rabbitmq.spec().rabbitmq_config().unwrap().advanced_config().is_some()
    && !rabbitmq.spec().rabbitmq_config().unwrap().advanced_config().unwrap().eq(&new_strlit("").to_string()) {
        data.insert(new_strlit("advanced.config").to_string(), rabbitmq.spec().rabbitmq_config().unwrap().advanced_config().unwrap());
    }
    if rabbitmq.spec().rabbitmq_config().is_some() && rabbitmq.spec().rabbitmq_config().unwrap().env_config().is_some()
    && !rabbitmq.spec().rabbitmq_config().unwrap().env_config().unwrap().eq(&new_strlit("").to_string()) {
        data.insert(new_strlit("rabbitmq-env.conf").to_string(), rabbitmq.spec().rabbitmq_config().unwrap().env_config().unwrap());
    }
    config_map.set_data(data);
    config_map
}

fn default_rbmq_config(rabbitmq: &RabbitmqCluster) -> (s: String)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        s@ == rabbitmq_spec::default_rbmq_config(rabbitmq@),
{
    new_strlit(
        "queue_master_locator = min-masters\n\
        disk_free_limit.absolute = 2GB\n\
        cluster_partition_handling = pause_minority\n\
        cluster_formation.peer_discovery_backend = rabbit_peer_discovery_k8s\n\
        cluster_formation.k8s.host = kubernetes.default\n\
        cluster_formation.k8s.address_type = hostname\n"
    ).to_string()
    .concat(new_strlit("cluster_formation.target_cluster_size_hint = "))
    .concat(i32_to_string(rabbitmq.spec().replicas()).as_str())
    .concat(new_strlit("\n"))
    .concat(new_strlit("cluster_name = "))
    .concat(rabbitmq.name().unwrap().as_str())
    .concat(new_strlit("\n"))
}

fn update_service_account(rabbitmq: &RabbitmqCluster, found_service_account: ServiceAccount) -> (service_account: ServiceAccount)
requires
    rabbitmq@.metadata.name.is_Some(),
    rabbitmq@.metadata.namespace.is_Some(),
ensures
    service_account@ == rabbitmq_spec::update_service_account(rabbitmq@, found_service_account@),
{
    let mut service_account = found_service_account.clone();
    let made_service_account = make_service_account(rabbitmq);
    service_account.set_metadata({
        let mut metadata = found_service_account.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_service_account.metadata().labels().unwrap());
        metadata.set_annotations(made_service_account.metadata().annotations().unwrap());
        metadata
    });
    service_account
}

fn make_service_account(rabbitmq: &RabbitmqCluster) -> (service_account: ServiceAccount)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service_account@ == rabbitmq_spec::make_service_account(rabbitmq@),
{
    let mut service_account = ServiceAccount::default();
    service_account.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(rabbitmq.name().unwrap().concat(new_strlit("-server")));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    service_account
}

fn update_role(rabbitmq: &RabbitmqCluster, found_role: Role) -> (role: Role)
requires
    rabbitmq@.metadata.name.is_Some(),
    rabbitmq@.metadata.namespace.is_Some(),
ensures
    role@ == rabbitmq_spec::update_role(rabbitmq@, found_role@),
{
    let mut role = found_role.clone();
    let made_role = make_role(rabbitmq);
    role.set_policy_rules(make_policy_rules(rabbitmq));
    role.set_metadata({
        let mut metadata = found_role.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_role.metadata().labels().unwrap());
        metadata.set_annotations(made_role.metadata().annotations().unwrap());
        metadata
    });
    role
}

fn make_policy_rules(rabbitmq: &RabbitmqCluster) -> (rules: Vec<PolicyRule>)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        rules@.map_values(|r: PolicyRule| r@) == rabbitmq_spec::make_role(rabbitmq@).policy_rules.get_Some_0(),
{
    let mut rules = Vec::new();
    rules.push({
        let mut rule = PolicyRule::default();
        rule.set_api_groups({
            let mut api_groups = Vec::new();
            api_groups.push(new_strlit("").to_string());
            proof{
                assert_seqs_equal!(
                    api_groups@.map_values(|p: String| p@),
                    rabbitmq_spec::make_role(rabbitmq@).policy_rules.get_Some_0()[0].api_groups.get_Some_0()
                );
            }
            api_groups
        });
        rule.set_resources({
            let mut resources = Vec::new();
            resources.push(new_strlit("endpoints").to_string());
            proof{
                assert_seqs_equal!(
                    resources@.map_values(|p: String| p@),
                    rabbitmq_spec::make_role(rabbitmq@).policy_rules.get_Some_0()[0].resources.get_Some_0()
                );
            }
            resources
        });
        rule.set_verbs({
            let mut verbs = Vec::new();
            verbs.push(new_strlit("get").to_string());
            proof{
                assert_seqs_equal!(
                    verbs@.map_values(|p: String| p@),
                    rabbitmq_spec::make_role(rabbitmq@).policy_rules.get_Some_0()[0].verbs
                );
            }
            verbs
        });
        rule
    });
    rules.push({
        let mut rule = PolicyRule::default();
        rule.set_api_groups({
            let mut api_groups = Vec::new();
            api_groups.push(new_strlit("").to_string());
            proof{
                assert_seqs_equal!(
                    api_groups@.map_values(|p: String| p@),
                    rabbitmq_spec::make_role(rabbitmq@).policy_rules.get_Some_0()[1].api_groups.get_Some_0()
                );
            }
            api_groups
        });
        rule.set_resources({
            let mut resources = Vec::new();
            resources.push(new_strlit("events").to_string());
            proof{
                assert_seqs_equal!(
                    resources@.map_values(|p: String| p@),
                    rabbitmq_spec::make_role(rabbitmq@).policy_rules.get_Some_0()[1].resources.get_Some_0()
                );
            }
            resources
        });
        rule.set_verbs({
            let mut verbs = Vec::new();
            verbs.push(new_strlit("create").to_string());
            proof{
                assert_seqs_equal!(
                    verbs@.map_values(|p: String| p@),
                    rabbitmq_spec::make_role(rabbitmq@).policy_rules.get_Some_0()[1].verbs
                );
            }
            verbs
        });
        rule
    });
    proof{
        assert_seqs_equal!(
            rules@.map_values(|p: PolicyRule| p@),
            rabbitmq_spec::make_role(rabbitmq@).policy_rules.get_Some_0()
        );
    }
    rules
}

fn make_role(rabbitmq: &RabbitmqCluster) -> (role: Role)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        role@ == rabbitmq_spec::make_role(rabbitmq@),
{
    let mut role = Role::default();
    role.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(rabbitmq.name().unwrap().concat(new_strlit("-peer-discovery")));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    role.set_policy_rules(make_policy_rules(rabbitmq));
    role
}

fn update_role_binding(rabbitmq: &RabbitmqCluster, found_role_binding: RoleBinding) -> (role_binding: RoleBinding)
requires
    rabbitmq@.metadata.name.is_Some(),
    rabbitmq@.metadata.namespace.is_Some(),
ensures
    role_binding@ == rabbitmq_spec::update_role_binding(rabbitmq@, found_role_binding@),
{
    let mut role_binding = found_role_binding.clone();
    let made_role_binding = make_role_binding(rabbitmq);
    role_binding.set_role_ref(make_role_ref(rabbitmq));
    role_binding.set_subjects(make_subjects(rabbitmq));
    role_binding.set_metadata({
        let mut metadata = found_role_binding.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_role_binding.metadata().labels().unwrap());
        metadata.set_annotations(made_role_binding.metadata().annotations().unwrap());
        metadata
    });
    role_binding
}

fn make_role_ref(rabbitmq: &RabbitmqCluster) -> (role_ref: RoleRef)
    requires
        rabbitmq@.metadata.name.is_Some(),
    ensures
        role_ref@ == rabbitmq_spec::make_role_binding(rabbitmq@).role_ref
{
    let mut role_ref = RoleRef::default();
    role_ref.set_api_group(new_strlit("rbac.authorization.k8s.io").to_string());
    role_ref.set_kind(new_strlit("Role").to_string());
    role_ref.set_name(rabbitmq.name().unwrap().concat(new_strlit("-peer-discovery")));
    role_ref
}

fn make_subjects(rabbitmq: &RabbitmqCluster) -> (subjects: Vec<Subject>)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        subjects@.map_values(|s: Subject| s@) == rabbitmq_spec::make_role_binding(rabbitmq@).subjects.get_Some_0(),
{
    let mut subjects = Vec::new();
    subjects.push({
        let mut subject = Subject::default();
        subject.set_kind(new_strlit("ServiceAccount").to_string());
        subject.set_name(rabbitmq.name().unwrap().concat(new_strlit("-server")));
        subject.set_namespace(rabbitmq.namespace().unwrap());
        subject
    });
    proof{
        assert_seqs_equal!(
            subjects@.map_values(|p: Subject| p@),
            rabbitmq_spec::make_role_binding(rabbitmq@).subjects.get_Some_0()
        );
    }
    subjects
}

fn make_role_binding(rabbitmq: &RabbitmqCluster) -> (role_binding: RoleBinding)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        role_binding@ == rabbitmq_spec::make_role_binding(rabbitmq@),
{
    let mut role_binding = RoleBinding::default();
    role_binding.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(rabbitmq.name().unwrap().concat(new_strlit("-server")));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    role_binding.set_role_ref(make_role_ref(rabbitmq));
    role_binding.set_subjects(make_subjects(rabbitmq));
    role_binding
}

fn update_stateful_set(rabbitmq: &RabbitmqCluster, found_stateful_set: StatefulSet, config_map_rv: &String) -> (stateful_set: StatefulSet)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
        found_stateful_set@.spec.is_Some(),
    ensures
        stateful_set@ == rabbitmq_spec::update_stateful_set(rabbitmq@, found_stateful_set@, config_map_rv@),
{
    let made_sts = make_stateful_set(rabbitmq, config_map_rv);

    let mut stateful_set = found_stateful_set.clone();
    stateful_set.set_spec({
        let mut sts_spec = found_stateful_set.spec().unwrap();
        let made_spec = made_sts.spec().unwrap();
        sts_spec.set_replicas(made_spec.replicas().unwrap());
        sts_spec.set_template(made_spec.template());
        sts_spec.overwrite_pvc_retention_policy(made_spec.persistent_volume_claim_retention_policy());
        sts_spec
    });
    stateful_set.set_metadata({
        let mut metadata = found_stateful_set.metadata();
        // Since we requirement the owner_reference only contains current cr, this set operation won't change anything.
        // Similarly, we never set finalizers for any stateful set, resetting finalizers won't change anything.
        // The reason why we add these two operations is that it makes the proof easier.
        // In this way, we can easily show that what the owner references and finalizers of the object in every update request
        // for stateful set are.
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_sts.metadata().labels().unwrap());
        metadata.set_annotations(made_sts.metadata().annotations().unwrap());
        metadata
    });
    stateful_set
}

fn sts_restart_annotation() -> (anno: String)
    ensures
        anno@ == rabbitmq_spec::sts_restart_annotation(),
{
    new_strlit("anvil.dev/lastRestartAt").to_string()
}

fn make_stateful_set_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        name@ == rabbitmq_spec::make_stateful_set_name(rabbitmq@.metadata.name.get_Some_0()),
{
    rabbitmq.name().unwrap().concat(new_strlit("-server"))
}

fn make_stateful_set(rabbitmq: &RabbitmqCluster, config_map_rv: &String) -> (stateful_set: StatefulSet)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        stateful_set@ == rabbitmq_spec::make_stateful_set(rabbitmq@, config_map_rv@),
{
    let mut stateful_set = StatefulSet::default();
    stateful_set.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_stateful_set_name(rabbitmq));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    stateful_set.set_spec({
        let mut stateful_set_spec = StatefulSetSpec::default();
        // Set the replicas number
        stateful_set_spec.set_replicas(rabbitmq.spec().replicas());
        // Set the headless service to assign DNS entry to each Rabbitmq server
        stateful_set_spec.set_service_name(rabbitmq.name().unwrap().concat(new_strlit("-nodes")));
        // Set the selector used for querying pods of this stateful set
        stateful_set_spec.set_selector({
            let mut selector = LabelSelector::default();
            selector.set_match_labels({
                let mut match_labels = StringMap::empty();
                match_labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
                match_labels
            });
            selector
        });
        // Set the templates used for creating the persistent volume claims attached to each pod
        stateful_set_spec.set_volume_claim_templates({ // TODO: Add PodManagementPolicy
            if rabbitmq.spec().persistence().storage().eq(&new_strlit("0Gi").to_string()) {
                let empty_pvc = Vec::<PersistentVolumeClaim>::new();
                proof {
                    assert_seqs_equal!(
                        empty_pvc@.map_values(|pvc: PersistentVolumeClaim| pvc@),
                        rabbitmq_spec::make_stateful_set(rabbitmq@, config_map_rv@).spec.get_Some_0().volume_claim_templates.get_Some_0()
                    );
                }
                empty_pvc
            } else {
                let mut volume_claim_templates = Vec::new();
                volume_claim_templates.push({
                    let mut pvc = PersistentVolumeClaim::default();
                    pvc.set_metadata({
                        let mut metadata = ObjectMeta::default();
                        metadata.set_name(new_strlit("persistence").to_string());
                        metadata.set_namespace(rabbitmq.namespace().unwrap());
                        metadata.set_labels({
                            let mut labels = StringMap::empty();
                            labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
                            labels
                        });
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
                                    rabbitmq_spec::make_stateful_set(rabbitmq@, config_map_rv@)
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
                                requests.insert(new_strlit("storage").to_string(), rabbitmq.spec().persistence().storage());
                                requests
                            });
                            resources
                        });
                        pvc_spec.overwrite_storage_class_name(rabbitmq.spec().persistence().storage_class_name());
                        pvc_spec
                    });
                    pvc
                });
                proof {
                    assert_seqs_equal!(
                        volume_claim_templates@.map_values(|pvc: PersistentVolumeClaim| pvc@),
                        rabbitmq_spec::make_stateful_set(rabbitmq@, config_map_rv@).spec.get_Some_0().volume_claim_templates.get_Some_0()
                    );
                }
                volume_claim_templates
            }
        });
        // Set the template used for creating pods
        stateful_set_spec.set_template({
            let mut pod_template_spec = PodTemplateSpec::default();
            pod_template_spec.set_metadata({
                let mut metadata = ObjectMeta::default();
                metadata.set_labels(make_labels(rabbitmq));
                metadata.set_annotations({
                    let mut anno = rabbitmq.spec().annotations();
                    anno.insert(sts_restart_annotation(), config_map_rv.clone());
                    anno
                });
                metadata
            });
            pod_template_spec.set_spec(make_rabbitmq_pod_spec(rabbitmq));
            pod_template_spec
        });
        // Set management policy
        if rabbitmq.spec().pod_management_policy().is_some() {
            stateful_set_spec.set_pod_management_policy(rabbitmq.spec().pod_management_policy().unwrap());
        } else {
            stateful_set_spec.set_pod_management_policy(new_strlit("Parallel").to_string());
        }

        if rabbitmq.spec().persistent_volume_claim_retention_policy().is_some() {
            stateful_set_spec.set_pvc_retention_policy(rabbitmq.spec().persistent_volume_claim_retention_policy().unwrap());
        }
        stateful_set_spec
    });
    stateful_set
}

fn make_rabbitmq_pod_spec(rabbitmq: &RabbitmqCluster) -> (pod_spec: PodSpec)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        pod_spec@ == rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@),
{
    let mut volumes = Vec::new();
    volumes.push({
        let mut volume = Volume::default();
        volume.set_name(new_strlit("plugins-conf").to_string());
        volume.set_config_map({
            let mut config_map = ConfigMapVolumeSource::default();
            config_map.set_name(rabbitmq.name().unwrap().concat(new_strlit("-plugins-conf")));
            config_map
        });
        volume
    });
    volumes.push({
        let mut volume = Volume::default();
        volume.set_name(new_strlit("rabbitmq-confd").to_string());
        volume.set_projected({
            let mut projected = ProjectedVolumeSource::default();
            projected.set_sources({
                let mut sources = Vec::new();
                sources.push({
                    let mut volume_projection = VolumeProjection::default();
                    volume_projection.set_config_map({
                        let mut config_map = ConfigMapProjection::default();
                        config_map.set_name(rabbitmq.name().unwrap().concat(new_strlit("-server-conf")));
                        config_map.set_items({
                            let mut items = Vec::new();
                            items.push({
                                let mut key_to_path = KeyToPath::default();
                                key_to_path.set_key(new_strlit("operatorDefaults.conf").to_string());
                                key_to_path.set_path(new_strlit("operatorDefaults.conf").to_string());
                                key_to_path
                            });
                            items.push({
                                let mut key_to_path = KeyToPath::default();
                                key_to_path.set_key(new_strlit("userDefinedConfiguration.conf").to_string());
                                key_to_path.set_path(new_strlit("userDefinedConfiguration.conf").to_string());
                                key_to_path
                            });
                            proof {
                                assert_seqs_equal!(
                                    items@.map_values(|item: KeyToPath| item@),
                                    rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()[1].projected.get_Some_0()
                                    .sources.get_Some_0()[0].config_map.get_Some_0().items.get_Some_0()
                                );
                            }
                            items
                        });
                        config_map
                    });
                    volume_projection
                });
                sources.push({
                    let mut volume_projection = VolumeProjection::default();
                    volume_projection.set_secret({
                        let mut secret = SecretProjection::default();
                        secret.set_name(rabbitmq.name().unwrap().concat(new_strlit("-default-user")));
                        secret.set_items({
                            let mut items = Vec::new();
                            items.push({
                                let mut key_to_path = KeyToPath::default();
                                key_to_path.set_key(new_strlit("default_user.conf").to_string());
                                key_to_path.set_path(new_strlit("default_user.conf").to_string());
                                key_to_path
                            });
                            proof {
                                assert_seqs_equal!(
                                    items@.map_values(|item: KeyToPath| item@),
                                    rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()[1].projected.get_Some_0()
                                    .sources.get_Some_0()[1].secret.get_Some_0().items.get_Some_0()
                                );
                            }
                            items
                        });
                        secret
                    });
                    volume_projection
                });
                proof {
                    assert_seqs_equal!(
                        sources@.map_values(|source: VolumeProjection| source@),
                        rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()[1].projected.get_Some_0()
                        .sources.get_Some_0()
                    );
                }
                sources
            });
            projected
        });
        volume
    });
    volumes.push({
        let mut volume = Volume::default();
        volume.set_name(new_strlit("rabbitmq-erlang-cookie").to_string());
        volume.set_empty_dir(EmptyDirVolumeSource::default());
        volume
    });
    volumes.push({
        let mut volume = Volume::default();
        volume.set_name(new_strlit("erlang-cookie-secret").to_string());
        volume.set_secret({
            let mut secret = SecretVolumeSource::default();
            secret.set_secret_name(rabbitmq.name().unwrap().concat(new_strlit("-erlang-cookie")));
            secret
        });
        volume
    });
    volumes.push({
        let mut volume = Volume::default();
        volume.set_name(new_strlit("rabbitmq-plugins").to_string());
        volume.set_empty_dir(EmptyDirVolumeSource::default());
        volume
    });
    volumes.push({
        let mut volume = Volume::default();
        volume.set_name(new_strlit("pod-info").to_string());
        volume.set_downward_api({
            let mut downward_api = DownwardAPIVolumeSource::default();
            downward_api.set_items({
                let mut items = Vec::new();
                items.push({
                    let mut downward_api_volume_file = DownwardAPIVolumeFile::default();
                    downward_api_volume_file.set_path(new_strlit("skipPreStopChecks").to_string());
                    downward_api_volume_file.set_field_ref({
                        let mut object_field_selector = ObjectFieldSelector::default();
                        object_field_selector.set_field_path(new_strlit("metadata.labels['skipPreStopChecks']").to_string());
                        object_field_selector
                    });
                    downward_api_volume_file
                });
                proof {
                    assert_seqs_equal!(
                        items@.map_values(|item: DownwardAPIVolumeFile| item@),
                        rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()[5].downward_api.get_Some_0().items.get_Some_0()
                    );
                }
                items
            });
            downward_api
        });
        volume
    });
    if rabbitmq.spec().persistence().storage().eq(&new_strlit("0Gi").to_string()) {
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("persistence").to_string());
            volume.set_empty_dir(EmptyDirVolumeSource::default());
            volume
        });
    }
    proof {
        assert_seqs_equal!(
            volumes@.map_values(|vol: Volume| vol@),
            rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()
        );
    }
    let mut pod_spec = PodSpec::default();
    pod_spec.set_service_account_name(rabbitmq.name().unwrap().concat(new_strlit("-server")));
    pod_spec.set_init_containers({
        let mut containers = Vec::new();
        containers.push({
            let mut rabbitmq_container = Container::default();
            rabbitmq_container.set_name(new_strlit("setup-container").to_string());
            rabbitmq_container.set_image(rabbitmq.spec().image());
            rabbitmq_container.set_command({
                let mut command = Vec::new();
                command.push(new_strlit("sh").to_string());
                command.push(new_strlit("-c").to_string());
                command.push(new_strlit("cp /tmp/erlang-cookie-secret/.erlang.cookie /var/lib/rabbitmq/.erlang.cookie && chmod 600 /var/lib/rabbitmq/.erlang.cookie ; cp /tmp/rabbitmq-plugins/enabled_plugins /operator/enabled_plugins ; echo '[default]' > /var/lib/rabbitmq/.rabbitmqadmin.conf && sed -e 's/default_user/username/' -e 's/default_pass/password/' /tmp/default_user.conf >> /var/lib/rabbitmq/.rabbitmqadmin.conf && chmod 600 /var/lib/rabbitmq/.rabbitmqadmin.conf ; sleep 30").to_string());
                proof {
                    let spec_cmd = seq![
                        new_strlit("sh")@,
                        new_strlit("-c")@,
                        new_strlit("cp /tmp/erlang-cookie-secret/.erlang.cookie /var/lib/rabbitmq/.erlang.cookie && chmod 600 /var/lib/rabbitmq/.erlang.cookie ; cp /tmp/rabbitmq-plugins/enabled_plugins /operator/enabled_plugins ; echo '[default]' > /var/lib/rabbitmq/.rabbitmqadmin.conf && sed -e 's/default_user/username/' -e 's/default_pass/password/' /tmp/default_user.conf >> /var/lib/rabbitmq/.rabbitmqadmin.conf && chmod 600 /var/lib/rabbitmq/.rabbitmqadmin.conf ; sleep 30")@
                    ];
                    assert_seqs_equal!(command@.map_values(|s: String| s@), spec_cmd);
                }
                command
            });
            rabbitmq_container.set_resources({
                let mut resources = ResourceRequirements::default();
                resources.set_limits({
                    let mut limits = StringMap::empty();
                    limits.insert(new_strlit("cpu").to_string(), new_strlit("100m").to_string());
                    limits.insert(new_strlit("memory").to_string(), new_strlit("500Mi").to_string());
                    limits
                });
                resources.set_requests({
                    let mut requests = StringMap::empty();
                    requests.insert(new_strlit("cpu").to_string(), new_strlit("100m").to_string());
                    requests.insert(new_strlit("memory").to_string(), new_strlit("500Mi").to_string());
                    requests
                });
                resources
            });
            rabbitmq_container.set_volume_mounts({
                let mut volume_mounts = Vec::new();
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("plugins-conf").to_string());
                    volume_mount.set_mount_path(new_strlit("/tmp/rabbitmq-plugins/").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("rabbitmq-erlang-cookie").to_string());
                    volume_mount.set_mount_path(new_strlit("/var/lib/rabbitmq/").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("erlang-cookie-secret").to_string());
                    volume_mount.set_mount_path(new_strlit("/tmp/erlang-cookie-secret/").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("rabbitmq-plugins").to_string());
                    volume_mount.set_mount_path(new_strlit("/operator").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("persistence").to_string());
                    volume_mount.set_mount_path(new_strlit("/var/lib/rabbitmq/mnesia/").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("rabbitmq-confd").to_string());
                    volume_mount.set_mount_path(new_strlit("/etc/pod-info/").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("rabbitmq-confd").to_string());
                    volume_mount.set_mount_path(new_strlit("/tmp/default_user.conf").to_string());
                    volume_mount.set_sub_path(new_strlit("default_user.conf").to_string());
                    volume_mount
                });

                proof {
                    assert_seqs_equal!(
                        volume_mounts@.map_values(|volume_mount: VolumeMount| volume_mount@),
                        rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).init_containers.unwrap()[0].volume_mounts.get_Some_0()
                    );
                }
                volume_mounts
            });
            rabbitmq_container
        });
        proof {
            assert_seqs_equal!(
                containers@.map_values(|container: Container| container@),
                rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).init_containers.unwrap()
            );
        }
        containers
    });
    pod_spec.set_containers({
        let mut containers = Vec::new();
        containers.push({
            let mut rabbitmq_container = Container::default();
            rabbitmq_container.overwrite_resources(rabbitmq.spec().resources());
            rabbitmq_container.set_name(new_strlit("rabbitmq").to_string());
            rabbitmq_container.set_image(rabbitmq.spec().image());
            rabbitmq_container.set_env(make_env_vars(&rabbitmq));
            rabbitmq_container.set_volume_mounts({
                let mut volume_mounts = Vec::new();
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("rabbitmq-erlang-cookie").to_string());
                    volume_mount.set_mount_path(new_strlit("/var/lib/rabbitmq/").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("persistence").to_string());
                    volume_mount.set_mount_path(new_strlit("/var/lib/rabbitmq/mnesia/").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("rabbitmq-plugins").to_string());
                    volume_mount.set_mount_path(new_strlit("/operator").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("rabbitmq-confd").to_string());
                    volume_mount.set_mount_path(new_strlit("/etc/rabbitmq/conf.d/10-operatorDefaults.conf").to_string());
                    volume_mount.set_sub_path(new_strlit("operatorDefaults.conf").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("rabbitmq-confd").to_string());
                    volume_mount.set_mount_path(new_strlit("/etc/rabbitmq/conf.d/90-userDefinedConfiguration.conf").to_string());
                    volume_mount.set_sub_path(new_strlit("userDefinedConfiguration.conf").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("pod-info").to_string());
                    volume_mount.set_mount_path(new_strlit("/etc/pod-info/").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("rabbitmq-confd").to_string());
                    volume_mount.set_mount_path(new_strlit("/etc/rabbitmq/conf.d/11-default_user.conf").to_string());
                    volume_mount.set_sub_path(new_strlit("default_user.conf").to_string());
                    volume_mount
                });
                proof {
                    assert_seqs_equal!(
                        volume_mounts@.map_values(|volume_mount: VolumeMount| volume_mount@),
                        rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).containers[0].volume_mounts.get_Some_0()
                    );
                }
                volume_mounts
            });
            rabbitmq_container.set_ports({
                let mut ports = Vec::new();
                ports.push(ContainerPort::new_with(new_strlit("epmd").to_string(), 4369));
                ports.push(ContainerPort::new_with(new_strlit("amqp").to_string(), 5672));
                ports.push(ContainerPort::new_with(new_strlit("management").to_string(), 15672));

                proof {
                    assert_seqs_equal!(
                        ports@.map_values(|port: ContainerPort| port@),
                        rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).containers[0].ports.get_Some_0()
                    );
                }

                ports
            });
            rabbitmq_container.set_readiness_probe({
                let mut probe = Probe::default();
                probe.set_failure_threshold(3);
                probe.set_initial_delay_seconds(50);
                probe.set_period_seconds(10);
                probe.set_success_threshold(1);
                probe.set_timeout_seconds(5);
                probe.set_tcp_socket({
                    let mut tcp_socket_action = TCPSocketAction::default();
                    tcp_socket_action.set_port(5672);
                    tcp_socket_action
                });
                probe
            });
            rabbitmq_container
        });
        proof {
            assert_seqs_equal!(
                containers@.map_values(|container: Container| container@),
                rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).containers
            );
        }
        containers
    });
    pod_spec.set_volumes(volumes);
    pod_spec.overwrite_affinity(rabbitmq.spec().affinity());
    pod_spec.overwrite_tolerations(rabbitmq.spec().tolerations());
    pod_spec
}

fn make_env_vars(rabbitmq: &RabbitmqCluster) -> (env_vars: Vec<EnvVar>)
    requires
        rabbitmq@.metadata.name.is_Some(),
    ensures
        env_vars@.map_values(|v: EnvVar| v@) == rabbitmq_spec::make_env_vars(rabbitmq@)
{
    let mut env_vars = Vec::new();
    env_vars.push(EnvVar::new_with(
        new_strlit("MY_POD_NAME").to_string(), None, Some(EnvVarSource::new_with_field_ref(
            ObjectFieldSelector::new_with(new_strlit("v1").to_string(), new_strlit("metadata.name").to_string())
        ))
    ));
    env_vars.push(EnvVar::new_with(
        new_strlit("MY_POD_NAMESPACE").to_string(), None, Some(EnvVarSource::new_with_field_ref(
            ObjectFieldSelector::new_with(new_strlit("v1").to_string(), new_strlit("metadata.namespace").to_string())
        ))
    ));
    env_vars.push(EnvVar::new_with(
        new_strlit("K8S_SERVICE_NAME").to_string(), Some(rabbitmq.name().unwrap().concat(new_strlit("-nodes"))), None
    ));
    env_vars.push(EnvVar::new_with(
        new_strlit("RABBITMQ_ENABLED_PLUGINS_FILE").to_string(), Some(new_strlit("/operator/enabled_plugins").to_string()), None
    ));
    env_vars.push(EnvVar::new_with(
        new_strlit("RABBITMQ_USE_LONGNAME").to_string(), Some(new_strlit("true").to_string()), None
    ));
    env_vars.push(EnvVar::new_with(
        new_strlit("RABBITMQ_NODENAME").to_string(), Some(new_strlit("rabbit@$(MY_POD_NAME).$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)").to_string()), None
    ));
    env_vars.push(EnvVar::new_with(
        new_strlit("K8S_HOSTNAME_SUFFIX").to_string(), Some(new_strlit(".$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)").to_string()), None
    ));
    proof {
        assert_seqs_equal!(
            env_vars@.map_values(|v: EnvVar| v@),
            rabbitmq_spec::make_env_vars(rabbitmq@)
        );
    }
    env_vars
}

}
