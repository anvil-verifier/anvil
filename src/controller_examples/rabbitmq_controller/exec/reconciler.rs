// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, label_selector::*, object_meta::*,
    persistent_volume_claim::*, pod::*, pod_template_spec::*, resource_requirements::*, role::*,
    role_binding::*, secret::*, service::*, stateful_set::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::rabbitmqcluster::*;
use crate::rabbitmq_controller::spec::reconciler as rabbitmq_spec;
use crate::reconciler::exec::*;
use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;
use vstd::vec::*;

verus! {

/// RabbitmqReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct RabbitmqReconcileState {
    // reconcile_step, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_step: RabbitmqReconcileStep,

    // The custom resource object that the controller is currently reconciling for
    pub rabbitmq: Option<RabbitmqCluster>,
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
impl Reconciler<RabbitmqCluster, RabbitmqReconcileState> for RabbitmqReconciler {
    fn reconcile_init_state(&self) -> RabbitmqReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, rabbitmq: &RabbitmqCluster, resp_o: Option<KubeAPIResponse>, state: RabbitmqReconcileState) -> (RabbitmqReconcileState, Option<KubeAPIRequest>) {
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
        state.to_view() == rabbitmq_spec::reconcile_init_state(), // aren't two functions the same?
{
    RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Init,
        rabbitmq: Option::None,
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

// TODO: make the shim layer pass rabbitmq, instead of rabbitmq_ref, to reconcile_core
pub fn reconcile_core(rabbitmq: &RabbitmqCluster, resp_o: Option<KubeAPIResponse>, state: RabbitmqReconcileState) -> (res: (RabbitmqReconcileState, Option<KubeAPIRequest>))
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        (res.0.to_view(), opt_req_to_view(&res.1)) == rabbitmq_spec::reconcile_core(rabbitmq@, opt_resp_to_view(&resp_o), state.to_view()),
{
    let step = state.reconcile_step;
    match step{
        RabbitmqReconcileStep::Init => {
            let headless_service = make_headless_service(&rabbitmq);
            let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                KubeCreateRequest {
                    api_resource: Service::api_resource(),
                    obj: headless_service.to_dynamic_object(),
                }
            ));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateHeadlessService,
                ..state
            };
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateHeadlessService => {
            let main_service = make_main_service(rabbitmq);
            let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                KubeCreateRequest {
                    api_resource: Service::api_resource(),
                    obj: main_service.to_dynamic_object(),
                }
            ));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateService,
                ..state
            };
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateService => {
            let erlang_secret = make_erlang_secret(rabbitmq);
            let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                KubeCreateRequest {
                    api_resource: Secret::api_resource(),
                    obj: erlang_secret.to_dynamic_object(),
                }
            ));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateErlangCookieSecret,
                ..state
            };
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateErlangCookieSecret => {
            let default_user_secret = make_default_user_secret(rabbitmq);
            let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                KubeCreateRequest {
                    api_resource: Secret::api_resource(),
                    obj: default_user_secret.to_dynamic_object(),
                }
            ));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateDefaultUserSecret,
                ..state
            };
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreateDefaultUserSecret => {
            let plugins_config_map = make_plugins_config_map(rabbitmq);
            let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                KubeCreateRequest {
                    api_resource: ConfigMap::api_resource(),
                    obj: plugins_config_map.to_dynamic_object(),
                }
            ));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreatePluginsConfigMap,
                ..state
            };
            return (state_prime, req_o);
        },
        RabbitmqReconcileStep::AfterCreatePluginsConfigMap => {
            let server_config_map = make_server_config_map(rabbitmq);
            let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                KubeCreateRequest {
                    api_resource: ConfigMap::api_resource(),
                    obj: server_config_map.to_dynamic_object(),
                }
            ));
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterCreateServerConfigMap,
                ..state
            };
            return (state_prime, req_o);
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

    make_service(rabbitmq, rabbitmq.name().unwrap(), ports, false)
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


    proof {
        assert_maps_equal!(
            data@,
            rabbitmq_spec::make_erlang_secret(rabbitmq@).data.get_Some_0()
        );
    }

    make_secret(rabbitmq, rabbitmq.name().unwrap().concat(new_strlit("-erlang-cookie")), data)
}

#[verifier(external_body)]
fn random_encoded_string(data_len: usize) -> (cookie: String)
    ensures
        cookie@ == rabbitmq_spec::random_encoded_string(data_len),
{
    let mut ret_string = new_strlit("").to_string().into_rust_string();
    for i in 0..data_len {
        let chunk = deps_hack::rand::random::<u8>();
        ret_string.push(chunk as char);
    }
    String::from_rust_string(ret_string)
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


    proof {
        assert_maps_equal!(
            data@,
            rabbitmq_spec::make_default_user_secret(rabbitmq@).data.get_Some_0()
        );
    }

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
    data.insert(new_strlit("userDefineConfiguration.conf").to_string(),
                new_strlit("total_memory_available_override_value = 1717986919\n").to_string());
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
    .concat(new_strlit("cluster_formation.target_cluster_size_hint = {}\n"))
    .concat(i32_to_string(rabbitmq.replica()).as_str())
    .concat(new_strlit("cluster_name = {}\n"))
    .concat(rabbitmq.name().unwrap().as_str())
}

}
