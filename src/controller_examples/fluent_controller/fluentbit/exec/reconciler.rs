// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::exec::types::*;
use crate::fluent_controller::fluentbit::spec::reconciler as fluent_spec;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, container::*, daemon_set::*, label_selector::*,
    object_meta::*, owner_reference::*, persistent_volume_claim::*, pod::*, pod_template_spec::*,
    resource::*, resource_requirements::*, role::*, role_binding::*, secret::*, service::*,
    service_account::*, toleration::*, volume::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

// TODO:
// + Use Role after Anvil supports cluster-scoped resources
//
// + Add more features
//
// + Split the management logic into two reconciliation loops

pub struct FluentBitReconcileState {
    pub reconcile_step: FluentBitReconcileStep,
}

impl FluentBitReconcileState {
    pub open spec fn to_view(&self) -> fluent_spec::FluentBitReconcileState {
        fluent_spec::FluentBitReconcileState {
            reconcile_step: self.reconcile_step,
        }
    }
}

pub struct FluentBitReconciler {}

#[verifier(external)]
impl Reconciler<FluentBit, FluentBitReconcileState, EmptyType, EmptyType, EmptyAPIShimLayer> for FluentBitReconciler {
    fn reconcile_init_state(&self) -> FluentBitReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, fluentbit: &FluentBit, resp_o: Option<Response<EmptyType>>, state: FluentBitReconcileState) -> (FluentBitReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(fluentbit, resp_o, state)
    }

    fn reconcile_done(&self, state: &FluentBitReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(&self, state: &FluentBitReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for FluentBitReconciler {
    fn default() -> FluentBitReconciler { FluentBitReconciler{} }
}

pub fn reconcile_init_state() -> (state: FluentBitReconcileState)
    ensures
        state.to_view() == fluent_spec::reconcile_init_state(),
{
    FluentBitReconcileState {
        reconcile_step: FluentBitReconcileStep::Init,
    }
}

pub fn reconcile_done(state: &FluentBitReconcileState) -> (res: bool)
    ensures
        res == fluent_spec::reconcile_done(state.to_view()),
{
    match state.reconcile_step {
        FluentBitReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &FluentBitReconcileState) -> (res: bool)
    ensures
        res == fluent_spec::reconcile_error(state.to_view()),
{
    match state.reconcile_step {
        FluentBitReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(fluentbit: &FluentBit, resp_o: Option<Response<EmptyType>>, state: FluentBitReconcileState) -> (res: (FluentBitReconcileState, Option<Request<EmptyType>>))
    requires
        fluentbit@.metadata.name.is_Some(),
        fluentbit@.metadata.namespace.is_Some(),
    ensures
        (res.0.to_view(), opt_request_to_view(&res.1)) == fluent_spec::reconcile_core(fluentbit@, opt_response_to_view(&resp_o), state.to_view()),
{
    let step = state.reconcile_step;
    match step{
        FluentBitReconcileStep::Init => {
            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: Secret::api_resource(),
                name: fluentbit.spec().fluentbit_config_name(),
                namespace: fluentbit.metadata().namespace().unwrap(),
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterGetSecret,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        FluentBitReconcileStep::AfterGetSecret => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_sts_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_sts_resp.is_ok() {
                    let role = make_role(fluentbit);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: Role::api_resource(),
                        namespace: fluentbit.metadata().namespace().unwrap(),
                        obj: role.marshal(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterCreateRole,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            // return error state
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        FluentBitReconcileStep::AfterCreateRole => {
            let service_account = make_service_account(fluentbit);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: ServiceAccount::api_resource(),
                namespace: fluentbit.metadata().namespace().unwrap(),
                obj: service_account.marshal(),
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterCreateServiceAccount,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        FluentBitReconcileStep::AfterCreateServiceAccount => {
            let role_binding = make_role_binding(fluentbit);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: RoleBinding::api_resource(),
                namespace: fluentbit.metadata().namespace().unwrap(),
                obj: role_binding.marshal(),
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterCreateRoleBinding,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        FluentBitReconcileStep::AfterCreateRoleBinding => {
            let daemon_set = make_daemon_set(fluentbit);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: DaemonSet::api_resource(),
                namespace: fluentbit.metadata().namespace().unwrap(),
                obj: daemon_set.marshal(),
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterCreateDaemonSet,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        FluentBitReconcileStep::AfterCreateDaemonSet => {
            let req_o = None;
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Done,
                ..state
            };
            (state_prime, req_o)
        },
        _ => {
            let state_prime = FluentBitReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = None;
            (state_prime, req_o)
        }
    }
}

fn make_role(fluentbit: &FluentBit) -> (role: Role)
    requires
        fluentbit@.metadata.name.is_Some(),
        fluentbit@.metadata.namespace.is_Some(),
    ensures
        role@ == fluent_spec::make_role(fluentbit@),
{
    let mut role = Role::default();
    role.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(fluentbit.metadata().name().unwrap().concat(new_strlit("-role")));
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(fluentbit.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    fluent_spec::make_role(fluentbit@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
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
                        fluent_spec::make_role(fluentbit@).policy_rules.get_Some_0()[0].api_groups.get_Some_0()
                    );
                }
                api_groups
            });
            rule.set_resources({
                let mut resources = Vec::new();
                resources.push(new_strlit("pods").to_string());
                proof{
                    assert_seqs_equal!(
                        resources@.map_values(|p: String| p@),
                        fluent_spec::make_role(fluentbit@).policy_rules.get_Some_0()[0].resources.get_Some_0()
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
                        fluent_spec::make_role(fluentbit@).policy_rules.get_Some_0()[0].verbs
                    );
                }
                verbs
            });
            rule
        });
        proof{
            assert_seqs_equal!(
                rules@.map_values(|p: PolicyRule| p@),
                fluent_spec::make_role(fluentbit@).policy_rules.get_Some_0()
            );
        }
        rules
    });
    role
}

fn make_service_account(fluentbit: &FluentBit) -> (service_account: ServiceAccount)
    requires
        fluentbit@.metadata.name.is_Some(),
        fluentbit@.metadata.namespace.is_Some(),
    ensures
        service_account@ == fluent_spec::make_service_account(fluentbit@),
{
    let mut service_account = ServiceAccount::default();
    service_account.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(fluentbit.metadata().name().unwrap());
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(fluentbit.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    fluent_spec::make_service_account(fluentbit@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });

    service_account
}

fn make_role_binding(fluentbit: &FluentBit) -> (role_binding: RoleBinding)
    requires
        fluentbit@.metadata.name.is_Some(),
        fluentbit@.metadata.namespace.is_Some(),
    ensures
        role_binding@ == fluent_spec::make_role_binding(fluentbit@),
{
    let mut role_binding = RoleBinding::default();
    role_binding.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(fluentbit.metadata().name().unwrap().concat(new_strlit("-role-binding")));
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(fluentbit.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    fluent_spec::make_role_binding(fluentbit@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    role_binding.set_role_ref({
        let mut role_ref = RoleRef::default();
        role_ref.set_api_group(new_strlit("rbac.authorization.k8s.io").to_string());
        role_ref.set_kind(new_strlit("Role").to_string());
        role_ref.set_name(fluentbit.metadata().name().unwrap().concat(new_strlit("-role")));
        role_ref
    });
    role_binding.set_subjects({
        let mut subjects = Vec::new();
        subjects.push({
            let mut subject = Subject::default();
            subject.set_kind(new_strlit("ServiceAccount").to_string());
            subject.set_name(fluentbit.metadata().name().unwrap());
            subject.set_namespace(fluentbit.metadata().namespace().unwrap());
            subject
        });
        proof{
            assert_seqs_equal!(
                subjects@.map_values(|p: Subject| p@),
                fluent_spec::make_role_binding(fluentbit@).subjects.get_Some_0()
            );
        }
        subjects
    });

    role_binding
}

fn make_daemon_set(fluentbit: &FluentBit) -> (daemon_set: DaemonSet)
    requires
        fluentbit@.metadata.name.is_Some(),
        fluentbit@.metadata.namespace.is_Some(),
    ensures
        daemon_set@ == fluent_spec::make_daemon_set(fluentbit@),
{
    let mut daemon_set = DaemonSet::default();
    daemon_set.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(fluentbit.metadata().name().unwrap());
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), fluentbit.metadata().name().unwrap());
            labels
        });
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(fluentbit.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    fluent_spec::make_daemon_set(fluentbit@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    daemon_set.set_spec({
        let mut daemon_set_spec = DaemonSetSpec::default();
        // Set the selector used for querying pods of this daemon set
        daemon_set_spec.set_selector({
            let mut selector = LabelSelector::default();
            selector.set_match_labels({
                let mut match_labels = StringMap::empty();
                match_labels.insert(new_strlit("app").to_string(), fluentbit.metadata().name().unwrap());
                match_labels
            });
            selector
        });
        // Set the template used for creating pods
        daemon_set_spec.set_template({
            let mut pod_template_spec = PodTemplateSpec::default();
            pod_template_spec.set_metadata({
                let mut metadata = ObjectMeta::default();
                metadata.set_labels({
                    let mut labels = StringMap::empty();
                    labels.insert(new_strlit("app").to_string(), fluentbit.metadata().name().unwrap());
                    labels
                });
                metadata
            });
            pod_template_spec.set_spec(make_fluentbit_pod_spec(fluentbit));
            pod_template_spec
        });
        daemon_set_spec
    });
    daemon_set
}

fn make_fluentbit_pod_spec(fluentbit: &FluentBit) -> (pod_spec: PodSpec)
    requires
        fluentbit@.metadata.name.is_Some(),
        fluentbit@.metadata.namespace.is_Some(),
    ensures
        pod_spec@ == fluent_spec::make_fluentbit_pod_spec(fluentbit@),
{
    let mut pod_spec = PodSpec::default();
    pod_spec.set_service_account_name(fluentbit.metadata().name().unwrap());
    pod_spec.set_containers({
        let mut containers = Vec::new();
        containers.push({
            let mut fluentbit_container = Container::default();
            fluentbit_container.set_name(new_strlit("fluent-bit").to_string());
            fluentbit_container.set_image(new_strlit("kubesphere/fluent-bit:v2.1.7").to_string());
            fluentbit_container.set_env(make_env(&fluentbit));
            fluentbit_container.set_volume_mounts({
                let mut volume_mounts = Vec::new();
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("varlibcontainers").to_string());
                    volume_mount.set_read_only(true);
                    volume_mount.set_mount_path(new_strlit("/containers").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("config").to_string());
                    volume_mount.set_read_only(true);
                    volume_mount.set_mount_path(new_strlit("/fluent-bit/config").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("varlogs").to_string());
                    volume_mount.set_read_only(true);
                    volume_mount.set_mount_path(new_strlit("/var/log/").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("systemd").to_string());
                    volume_mount.set_read_only(true);
                    volume_mount.set_mount_path(new_strlit("/var/log/journal").to_string());
                    volume_mount
                });
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("positions").to_string());
                    volume_mount.set_mount_path(new_strlit("/fluent-bit/tail").to_string());
                    volume_mount
                });
                proof {
                    assert_seqs_equal!(
                        volume_mounts@.map_values(|volume_mount: VolumeMount| volume_mount@),
                        fluent_spec::make_fluentbit_pod_spec(fluentbit@).containers[0].volume_mounts.get_Some_0()
                    );
                }
                volume_mounts
            });
            fluentbit_container.set_ports({
                let mut ports = Vec::new();
                ports.push(ContainerPort::new_with(new_strlit("metrics").to_string(), 2020));
                proof {
                    assert_seqs_equal!(
                        ports@.map_values(|port: ContainerPort| port@),
                        fluent_spec::make_fluentbit_pod_spec(fluentbit@).containers[0].ports.get_Some_0()
                    );
                }
                ports
            });
            fluentbit_container.overwrite_resources(fluentbit.spec().resources());
            fluentbit_container
        });
        proof {
            assert_seqs_equal!(
                containers@.map_values(|container: Container| container@),
                fluent_spec::make_fluentbit_pod_spec(fluentbit@).containers
            );
        }
        containers
    });
    pod_spec.set_volumes({
        let mut volumes = Vec::new();
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("varlibcontainers").to_string());
            volume.set_host_path({
                let mut host_path = HostPathVolumeSource::default();
                host_path.set_path(new_strlit("/containers").to_string());
                host_path
            });
            volume
        });
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("config").to_string());
            volume.set_secret({
                let mut secret = SecretVolumeSource::default();
                secret.set_secret_name(fluentbit.spec().fluentbit_config_name());
                secret
            });
            volume
        });
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("varlogs").to_string());
            volume.set_host_path({
                let mut host_path = HostPathVolumeSource::default();
                host_path.set_path(new_strlit("/var/log").to_string());
                host_path
            });
            volume
        });
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("systemd").to_string());
            volume.set_host_path({
                let mut host_path = HostPathVolumeSource::default();
                host_path.set_path(new_strlit("/var/log/journal").to_string());
                host_path
            });
            volume
        });
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("positions").to_string());
            volume.set_host_path({
                let mut host_path = HostPathVolumeSource::default();
                host_path.set_path(new_strlit("/var/lib/fluent-bit/").to_string());
                host_path
            });
            volume
        });
        proof {
            assert_seqs_equal!(
                volumes@.map_values(|vol: Volume| vol@),
                fluent_spec::make_fluentbit_pod_spec(fluentbit@).volumes.get_Some_0()
            );
        }
        volumes
    });
    pod_spec.overwrite_tolerations(fluentbit.spec().tolerations());
    pod_spec
}

#[verifier(external_body)]
fn make_env(fluentbit: &FluentBit) -> Vec<EnvVar> {
    let mut env_vars = Vec::new();
    env_vars.push(
        EnvVar::from_kube(
            deps_hack::k8s_openapi::api::core::v1::EnvVar {
                name: new_strlit("NODE_NAME").to_string().into_rust_string(),
                value_from: Some(deps_hack::k8s_openapi::api::core::v1::EnvVarSource {
                    field_ref: Some(deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector {
                        field_path: new_strlit("spec.nodeName").to_string().into_rust_string(),
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
                name: new_strlit("HOST_IP").to_string().into_rust_string(),
                value_from: Some(deps_hack::k8s_openapi::api::core::v1::EnvVarSource {
                    field_ref: Some(deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector {
                        field_path: new_strlit("status.hostIP").to_string().into_rust_string(),
                        ..deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector::default()
                    }),
                    ..deps_hack::k8s_openapi::api::core::v1::EnvVarSource::default()
                }),
                ..deps_hack::k8s_openapi::api::core::v1::EnvVar::default()
            }
        )
    );
    env_vars
}

}
