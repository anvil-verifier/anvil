// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, label_selector::*, object_meta::*,
    persistent_volume_claim::*, pod::*, pod_template_spec::*, resource_requirements::*, role::*,
    role_binding::*, secret::*, service::*, service_account::*, stateful_set::*,
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
        metadata.set_name(rabbitmq.name().unwrap().concat(new_strlit("-peer-discorvery")));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), rabbitmq.name().unwrap());
            labels
        });
        metadata
    });
    role.set_policy_rules({
        let mut rules = Vec::empty();
        rules.push({
            let mut rule = PolicyRule::default();
            rule.set_api_groups({
                let mut api_groups = Vec::empty();
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
                let mut resources = Vec::empty();
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
                let mut verbs = Vec::empty();
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
                let mut api_groups = Vec::empty();
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
                let mut resources = Vec::empty();
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
                let mut verbs = Vec::empty();
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
        role_ref.set_name(rabbitmq.name().unwrap().concat(new_strlit("-peer-discorvery")));
        role_ref
    });
    role_binding.set_subjects({
        let mut subjects = Vec::empty();
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
        // Set the replica number
        stateful_set_spec.set_replicas(rabbitmq.replica());
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
            // pod_template_spec.set_spec(make_rabbitmq_pod_spec(rabbitmq));
            pod_template_spec
        });
        // Set the templates used for creating the persistent volume claims attached to each pod
        stateful_set_spec.set_volume_claim_templates({ // TODO: Add PodManagementPolicy
            let mut volume_claim_templates = Vec::empty();
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
                        let mut access_modes = Vec::empty();
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
                    // pvc_spec.set_resources(make_resource_requirements());
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
        stateful_set_spec
    });
    stateful_set
}


fn make_rabbitmq_pod_spec(rabbitmq: &RabbitmqCluster) -> (pod_spec: PodSpec)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        // pod_spec@ == rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@),
{
    // let mut volumes = Vec::empty();
    // volumes.push({
    //     let mut volume = Volume::default();
    //     volume.set_name(new_strlit("plugins-conf").to_string());
    //     volume.set_config_map({
    //         let mut config_map = ConfigMapVolumeSource::default();
    //         config_map.set_name(rabbitmq.name().unwrap().concat(new_strlit("-plugins-conf")));
    //         config_map
    //     });
    //     volume
    // }).push({
    //     let mut volume = Volume::default();
    //     volume.set_name(new_strlit("rabbitmq-confd").to_string());
    //     volume.set_config_map({
    //         let mut config_map = ConfigMapVolumeSource::default();
    //         config_map.set_name(rabbitmq.name().unwrap().concat(new_strlit("-configmap")));
    //         config_map
    //     });
    //     volume
    // }).push({
    //     let mut volume = Volume::default();
    //     volume.set_name(new_strlit("conf").to_string());
    //     volume.set_config_map({
    //         let mut config_map = ConfigMapVolumeSource::default();
    //         config_map.set_name(rabbitmq.name().unwrap().concat(new_strlit("-configmap")));
    //         config_map
    //     });
    //     volume
    // }).push({
    //     let mut volume = Volume::default();
    //     volume.set_name(new_strlit("conf").to_string());
    //     volume.set_config_map({
    //         let mut config_map = ConfigMapVolumeSource::default();
    //         config_map.set_name(rabbitmq.name().unwrap().concat(new_strlit("-configmap")));
    //         config_map
    //     });
    //     volume
    // });

    // proof {
    //     assert_seqs_equal!(
    //         volumes@.map_values(|vol: Volume| vol@),
    //         rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()
    //     );
    // }



    let mut pod_spec = PodSpec::default();

    pod_spec.set_containers({
        let mut containers = Vec::empty();
        containers.push({
            let mut rabbitmq_container = Container::default();
            rabbitmq_container.set_name(new_strlit("rabbitmq").to_string());
            rabbitmq_container.set_image(new_strlit("rabbitmq:3.11.10-management").to_string());
            rabbitmq_container.set_command({
                let mut command = Vec::empty();
                command.push(new_strlit("/usr/local/bin/RabbitmqStart.sh").to_string());
                command
            });
            // TODO: rabbitmq_container.set_resources();
            // rabbitmq_container.set_image_pull_policy(new_strlit("Always").to_string());
            // rabbitmq_container.set_volume_mounts({
            //     let mut volume_mounts = Vec::empty();
            //     volume_mounts.push({
            //         let mut data_volume_mount = VolumeMount::default();
            //         data_volume_mount.set_name(new_strlit("data").to_string());
            //         data_volume_mount.set_mount_path(new_strlit("/data").to_string());
            //         data_volume_mount
            //     });
            //     volume_mounts.push({
            //         let mut conf_volume_mount = VolumeMount::default();
            //         conf_volume_mount.set_name(new_strlit("conf").to_string());
            //         conf_volume_mount.set_mount_path(new_strlit("/conf").to_string());
            //         conf_volume_mount
            //     });

            //     proof {
            //         assert_seqs_equal!(
            //             volume_mounts@.map_values(|volume_mount: VolumeMount| volume_mount@),
            //             rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).containers[0].volume_mounts.get_Some_0()
            //         );
            //     }

            //     volume_mounts
            // });
            // rabbitmq_container.set_ports({
            //     let mut ports = Vec::empty();
            //     ports.push(ContainerPort::new_with(new_strlit("client").to_string(), 2181));
            //     ports.push(ContainerPort::new_with(new_strlit("quorum").to_string(), 2888));
            //     ports.push(ContainerPort::new_with(new_strlit("leader-election").to_string(), 3888));
            //     ports.push(ContainerPort::new_with(new_strlit("metrics").to_string(), 7000));
            //     ports.push(ContainerPort::new_with(new_strlit("admin-server").to_string(), 8080));

            //     proof {
            //         assert_seqs_equal!(
            //             ports@.map_values(|port: ContainerPort| port@),
            //             rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).containers[0].ports.get_Some_0()
            //         );
            //     }

            //     ports
            // });
            // rabbitmq_container.set_readiness_probe(make_readiness_probe());
            // rabbitmq_container.set_liveness_probe(make_liveness_probe());
            rabbitmq_container
        });

        // proof {
        //     assert_seqs_equal!(
        //         containers@.map_values(|container: Container| container@),
        //         rabbitmq_spec::make_rabbitmq_pod_spec(rabbitmq@).containers
        //     );
        // }

        containers
    });
    // pod_spec.set_volumes(volumes);

    pod_spec
}

}
