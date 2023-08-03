// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, label_selector::*, object_meta::*,
    persistent_volume_claim::*, pod::*, pod_template_spec::*, resource::*,
    resource_requirements::*, role::*, role_binding::*, secret::*, service::*, service_account::*,
    stateful_set::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::rabbitmqcluster::*;
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
}

impl RabbitmqReconcileState {
    pub open spec fn to_view(&self) -> rabbitmq_spec::RabbitmqReconcileState {
        rabbitmq_spec::RabbitmqReconcileState {
                reconcile_step: self.reconcile_step,
        }
    }
}

pub struct RabbitmqReconciler {}

#[verifier(external)]
impl Reconciler<RabbitmqCluster, RabbitmqReconcileState, EmptyType, EmptyType, EmptyAPI> for RabbitmqReconciler {
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
            let headless_service = make_headless_service(&rabbitmq);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: Service::api_resource(),
                namespace: rabbitmq.namespace().unwrap(),
                obj: headless_service.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateHeadlessService,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterCreateHeadlessService => {
            let main_service = make_main_service(rabbitmq);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: Service::api_resource(),
                namespace: rabbitmq.namespace().unwrap(),
                obj: main_service.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateService,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterCreateService => {
            let erlang_secret = make_erlang_secret(rabbitmq);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: Secret::api_resource(),
                namespace: rabbitmq.namespace().unwrap(),
                obj: erlang_secret.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateErlangCookieSecret,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterCreateErlangCookieSecret => {
            let default_user_secret = make_default_user_secret(rabbitmq);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: Secret::api_resource(),
                namespace: rabbitmq.namespace().unwrap(),
                obj: default_user_secret.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateDefaultUserSecret,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterCreateDefaultUserSecret => {
            let plugins_config_map = make_plugins_config_map(rabbitmq);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: ConfigMap::api_resource(),
                namespace: rabbitmq.namespace().unwrap(),
                obj: plugins_config_map.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreatePluginsConfigMap,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterCreatePluginsConfigMap => {
            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: ConfigMap::api_resource(),
                    name: rabbitmq.name().unwrap().concat(new_strlit("-server-conf")),
                    namespace: rabbitmq.namespace().unwrap(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterGetServerConfigMap,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterGetServerConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let config_map = make_server_config_map(rabbitmq);
                let get_config_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_config_resp.is_ok() {
                    // update
                    let found_config_map = ConfigMap::from_dynamic_object(get_config_resp.unwrap());
                    if found_config_map.is_ok(){
                        let mut new_config_map = found_config_map.unwrap();
                        new_config_map.set_data(config_map.data().unwrap());
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: ConfigMap::api_resource(),
                            name: config_map.metadata().name().unwrap(),
                            namespace: rabbitmq.namespace().unwrap(),
                            obj: new_config_map.to_dynamic_object(),
                        });
                        let state_prime = RabbitmqReconcileState {
                            reconcile_step: RabbitmqReconcileStep::AfterUpdateServerConfigMap,
                            ..state
                        };
                        return (state_prime, Option::Some(Request::KRequest(req_o)));
                    }
                } else if get_config_resp.unwrap_err().is_object_not_found() {
                    // create
                    let server_config_map = make_server_config_map(rabbitmq);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: ConfigMap::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: server_config_map.to_dynamic_object(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateServerConfigMap,
                        ..state
                    };
                    return (state_prime, Option::Some(Request::KRequest(req_o)));
                }

            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = Option::None;
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterUpdateServerConfigMap => {
            let service_account = make_service_account(rabbitmq);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: ServiceAccount::api_resource(),
                namespace: rabbitmq.namespace().unwrap(),
                obj: service_account.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateServiceAccount,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterCreateServerConfigMap => {
            let service_account = make_service_account(rabbitmq);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: ServiceAccount::api_resource(),
                namespace: rabbitmq.namespace().unwrap(),
                obj: service_account.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateServiceAccount,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterCreateServiceAccount => {
            let role = make_role(rabbitmq);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: Role::api_resource(),
                namespace: rabbitmq.namespace().unwrap(),
                obj: role.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateRole,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterCreateRole => {
            let role_binding = make_role_binding(rabbitmq);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: RoleBinding::api_resource(),
                namespace: rabbitmq.namespace().unwrap(),
                obj: role_binding.to_dynamic_object(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateRoleBinding,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterCreateRoleBinding => {
            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: StatefulSet::api_resource(),
                name: rabbitmq.name().unwrap().concat(new_strlit("-server")),
                namespace: rabbitmq.namespace().unwrap(),
            });
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterGetStatefulSet,
                ..state
            };
            return (state_prime, Option::Some(Request::KRequest(req_o)));
        },
        RabbitmqReconcileStep::AfterGetStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let stateful_set = make_stateful_set(rabbitmq);
                let get_sts_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_sts_resp.is_ok() {
                    // update
                    let found_stateful_set = StatefulSet::from_dynamic_object(get_sts_resp.unwrap());
                    if found_stateful_set.is_ok(){
                        let mut new_stateful_set = found_stateful_set.unwrap();
                        // rabbitmq controller doesn't support scale down, so new replicas must be greater than or equal to old replicas
                        if new_stateful_set.spec().is_some()
                            && new_stateful_set.spec().unwrap().replicas().is_some()
                            && new_stateful_set.spec().unwrap().replicas().unwrap() <= rabbitmq.spec().replicas() {
                                new_stateful_set.set_spec(stateful_set.spec().unwrap());
                                let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                                    api_resource: StatefulSet::api_resource(),
                                    name: stateful_set.metadata().name().unwrap(),
                                    namespace: rabbitmq.namespace().unwrap(),
                                    obj: new_stateful_set.to_dynamic_object(),
                                });
                                let state_prime = RabbitmqReconcileState {
                                    reconcile_step: RabbitmqReconcileStep::AfterUpdateStatefulSet,
                                    ..state
                                };
                                return (state_prime, Option::Some(Request::KRequest(req_o)));
                        }
                    }
                } else if get_sts_resp.unwrap_err().is_object_not_found() {
                    // create
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: StatefulSet::api_resource(),
                        namespace: rabbitmq.namespace().unwrap(),
                        obj: stateful_set.to_dynamic_object(),
                    });
                    let state_prime = RabbitmqReconcileState {
                        reconcile_step: RabbitmqReconcileStep::AfterCreateStatefulSet,
                        ..state
                    };
                    return (state_prime, Option::Some(Request::KRequest(req_o)));
                }

            }
            // return error state
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Error,
                ..state
            };
            let req_o = Option::None;
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateStatefulSet => {
            let req_o = Option::None;
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            (state_prime, req_o)
        },
        RabbitmqReconcileStep::AfterUpdateStatefulSet => {
            let req_o = Option::None;
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            (state_prime, req_o)
        },
        _ => {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = Option::None;
            (state_prime, req_o)
        }
    }
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

pub fn make_main_service(rabbitmq: &RabbitmqCluster) -> (service: Service)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service@ == rabbitmq_spec::make_main_service(rabbitmq@)
{
    let mut ports = Vec::new();
    ports.push({
        let mut temp = ServicePort::new_with(new_strlit("amqp").to_string(), 5672);
        temp.set_app_protocol(new_strlit("amqp").to_string());
        temp
    }
    );
    ports.push({
        let mut temp = ServicePort::new_with(new_strlit("management").to_string(), 15672);
        temp.set_app_protocol(new_strlit("http").to_string());
        temp
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
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            labels
        });
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

pub fn make_erlang_secret(rabbitmq: &RabbitmqCluster) -> (secret: Secret)
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

pub fn make_default_user_secret(rabbitmq: &RabbitmqCluster) -> (secret: Secret)
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
    data.insert(new_strlit("default_user.conf").to_string(), new_strlit("default_user = user\ndefault_pass = changeme").to_string());
    data.insert(new_strlit(".port").to_string(), new_strlit("5672").to_string());
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
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            labels
        });
        metadata
    });
    secret.set_data(data);
    secret
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
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            labels
        });
        metadata
    });
    let mut data = StringMap::empty();
    data.insert(new_strlit("enabled_plugins").to_string(),
                new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_management].").to_string());
    config_map.set_data(data);
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
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            labels
        });
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
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            labels
        });
        metadata
    });
    service_account
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
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            labels
        });
        metadata
    });
    role.set_policy_rules({
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
    });
    role
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
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            labels
        });
        metadata
    });
    role_binding.set_role_ref({
        let mut role_ref = RoleRef::default();
        role_ref.set_api_group(new_strlit("rbac.authorization.k8s.io").to_string());
        role_ref.set_kind(new_strlit("Role").to_string());
        role_ref.set_name(rabbitmq.name().unwrap().concat(new_strlit("-peer-discovery")));
        role_ref
    });
    role_binding.set_subjects({
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
    });
    role_binding
}

fn make_stateful_set(rabbitmq: &RabbitmqCluster) -> (stateful_set: StatefulSet)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        stateful_set@ == rabbitmq_spec::make_stateful_set(rabbitmq@),
{
    let mut stateful_set = StatefulSet::default();
    stateful_set.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(rabbitmq.name().unwrap().concat(new_strlit("-server")));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            labels
        });
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
                                rabbitmq_spec::make_stateful_set(rabbitmq@)
                                    .spec.get_Some_0().volume_claim_templates.get_Some_0()[0]
                                    .spec.get_Some_0().access_modes.get_Some_0()
                            );
                        }

                        access_modes
                    });
                    pvc_spec.set_resources(make_pvc_resource_requirements());
                    pvc_spec
                });
                pvc
            });
            proof {
                assert_seqs_equal!(
                    volume_claim_templates@.map_values(|pvc: PersistentVolumeClaim| pvc@),
                    rabbitmq_spec::make_stateful_set(rabbitmq@).spec.get_Some_0().volume_claim_templates.get_Some_0()
                );
            }
            volume_claim_templates
        });
        // Set management policy
        stateful_set_spec.set_pod_management_policy(new_strlit("Parallel").to_string());
        // Set the template used for creating pods
        stateful_set_spec.set_template({
            let mut pod_template_spec = PodTemplateSpec::default();
            pod_template_spec.set_metadata({
                let mut metadata = ObjectMeta::default();
                metadata.set_labels({
                    let mut labels = StringMap::empty();
                    labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
                    labels
                });
                metadata
            });
            pod_template_spec.set_spec(make_rabbitmq_pod_spec(rabbitmq));
            pod_template_spec
        });
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
        volume.set_empty_dir();
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
        volume.set_empty_dir();
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
            rabbitmq_container.set_image(new_strlit("rabbitmq:3.11.10-management").to_string());
            rabbitmq_container.set_command({
                let mut command = Vec::new();
                command.push(new_strlit("sh").to_string());
                command.push(new_strlit("-c").to_string());
                command.push(new_strlit("cp /tmp/erlang-cookie-secret/.erlang.cookie /var/lib/rabbitmq/.erlang.cookie && chmod 600 /var/lib/rabbitmq/.erlang.cookie ; cp /tmp/rabbitmq-plugins/enabled_plugins /operator/enabled_plugins ; echo '[default]' > /var/lib/rabbitmq/.rabbitmqadmin.conf && sed -e 's/default_user/username/' -e 's/default_pass/password/' /tmp/default_user.conf >> /var/lib/rabbitmq/.rabbitmqadmin.conf && chmod 600 /var/lib/rabbitmq/.rabbitmqadmin.conf ; sleep 30").to_string());
                command
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
            rabbitmq_container.set_name(new_strlit("rabbitmq").to_string());
            rabbitmq_container.set_image(new_strlit("rabbitmq:3.11.10-management").to_string());
            rabbitmq_container.set_env(make_env_vars(&rabbitmq));
            // rabbitmq_container.set_resources(make_container_resource_requirements());
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
            rabbitmq_container.set_readiness_probe(make_readiness_probe());
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
    pod_spec
}

#[verifier(external_body)]
fn make_readiness_probe() -> Probe
{
    Probe::from_kube(
        deps_hack::k8s_openapi::api::core::v1::Probe {
            failure_threshold: std::option::Option::Some(3),
            initial_delay_seconds: std::option::Option::Some(50),
            period_seconds: std::option::Option::Some(10),
            success_threshold: std::option::Option::Some(1),
            timeout_seconds: std::option::Option::Some(5),
            tcp_socket: std::option::Option::Some(deps_hack::k8s_openapi::api::core::v1::TCPSocketAction{
                port: deps_hack::k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::String(new_strlit("amqp").to_string().into_rust_string()),
                ..deps_hack::k8s_openapi::api::core::v1::TCPSocketAction::default()
            }),
            ..deps_hack::k8s_openapi::api::core::v1::Probe::default()
        }
    )
}

#[verifier(external_body)]
fn make_env_vars(rabbitmq: &RabbitmqCluster) -> Vec<EnvVar> {
    let mut env_vars = Vec::new();
    env_vars.push(
        EnvVar::from_kube(
            deps_hack::k8s_openapi::api::core::v1::EnvVar {
            name: new_strlit("MY_POD_NAME").to_string().into_rust_string(),
            value_from: std::option::Option::Some(deps_hack::k8s_openapi::api::core::v1::EnvVarSource {
                field_ref: std::option::Option::Some(deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector {
                    field_path: new_strlit("metadata.name").to_string().into_rust_string(),
                    api_version: std::option::Option::Some(new_strlit("v1").to_string().into_rust_string()),
                    ..deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector::default()
                }),
                ..deps_hack::k8s_openapi::api::core::v1::EnvVarSource::default()
            }),
            ..deps_hack::k8s_openapi::api::core::v1::EnvVar::default()
        }
        )
    );
    env_vars.push(
        EnvVar::from_kube(
            deps_hack::k8s_openapi::api::core::v1::EnvVar {
            name: new_strlit("MY_POD_NAMESPACE").to_string().into_rust_string(),
            value_from: std::option::Option::Some(deps_hack::k8s_openapi::api::core::v1::EnvVarSource {
                field_ref: std::option::Option::Some(deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector {
                    field_path: new_strlit("metadata.namespace").to_string().into_rust_string(),
                    api_version: std::option::Option::Some( new_strlit("v1").to_string().into_rust_string()),
                    ..deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector::default()
                }),
                ..deps_hack::k8s_openapi::api::core::v1::EnvVarSource::default()
            }),
            ..deps_hack::k8s_openapi::api::core::v1::EnvVar::default()
            }
        )
    );
    env_vars.push(
        EnvVar::from_kube(
            deps_hack::k8s_openapi::api::core::v1::EnvVar {
            name: new_strlit("K8S_SERVICE_NAME").to_string().into_rust_string(),
            value: std::option::Option::Some(rabbitmq.name().unwrap().concat(new_strlit("-nodes")).into_rust_string() ),
            ..deps_hack::k8s_openapi::api::core::v1::EnvVar::default()
            }
        )
    );
    env_vars.push(
        EnvVar::from_kube(
            deps_hack::k8s_openapi::api::core::v1::EnvVar {
                name: new_strlit("RABBITMQ_ENABLED_PLUGINS_FILE").to_string().into_rust_string(),
                value: std::option::Option::Some(new_strlit("/operator/enabled_plugins").to_string().into_rust_string()),
                ..deps_hack::k8s_openapi::api::core::v1::EnvVar::default()
            },
        )
    );
    env_vars.push(
        EnvVar::from_kube(
            deps_hack::k8s_openapi::api::core::v1::EnvVar {
                name: new_strlit("RABBITMQ_USE_LONGNAME").to_string().into_rust_string(),
                value: std::option::Option::Some(new_strlit("true").to_string().into_rust_string()),
                ..deps_hack::k8s_openapi::api::core::v1::EnvVar::default()
            },
        )
    );
    env_vars.push(
        EnvVar::from_kube(
            deps_hack::k8s_openapi::api::core::v1::EnvVar {
                name: new_strlit("RABBITMQ_NODENAME").to_string().into_rust_string(),
                value: std::option::Option::Some(new_strlit("rabbit@$(MY_POD_NAME).$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)").to_string().into_rust_string()),
                ..deps_hack::k8s_openapi::api::core::v1::EnvVar::default()
            },
        )
    );
    env_vars.push(
        EnvVar::from_kube(
            deps_hack::k8s_openapi::api::core::v1::EnvVar {
                name: new_strlit("K8S_HOSTNAME_SUFFIX").to_string().into_rust_string(),
                value: std::option::Option::Some(new_strlit(".$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)").to_string().into_rust_string()),
                ..deps_hack::k8s_openapi::api::core::v1::EnvVar::default()
            },
        )
    );
    env_vars
}

#[verifier(external_body)]
fn make_pvc_resource_requirements() -> ResourceRequirements
{
    ResourceRequirements::from_kube(
        deps_hack::k8s_openapi::api::core::v1::ResourceRequirements {
            requests: std::option::Option::Some(std::collections::BTreeMap::from([(
                "storage".to_string(),
                deps_hack::k8s_openapi::apimachinery::pkg::api::resource::Quantity("10Gi".to_string()),
            )])),
            ..deps_hack::k8s_openapi::api::core::v1::ResourceRequirements::default()
        }
    )
}

}
