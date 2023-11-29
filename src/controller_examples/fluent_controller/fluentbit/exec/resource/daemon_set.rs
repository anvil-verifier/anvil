// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::model::resource as model_resource;
use crate::fluent_controller::fluentbit::trusted::{
    exec_types::*, spec_types::FluentBitView, step::*,
};
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct DaemonSetBuilder {}

impl ResourceBuilder<FluentBit, FluentBitReconcileState, model_resource::DaemonSetBuilder> for DaemonSetBuilder {
    open spec fn requirements(fb: FluentBitView) -> bool {
        fb.well_formed()
    }

    fn get_request(fb: &FluentBit) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: DaemonSet::api_resource(),
            name: make_daemon_set_name(fb),
            namespace: fb.metadata().namespace().unwrap(),
        }
    }

    fn make(fb: &FluentBit, state: &FluentBitReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_daemon_set(fb).marshal())
    }

    fn update(fb: &FluentBit, state: &FluentBitReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let ds = DaemonSet::unmarshal(obj);
        if ds.is_ok() {
            let found_ds = ds.unwrap();
            if found_ds.metadata().owner_references_only_contains(fb.controller_owner_ref()) && found_ds.spec().is_some() {
                return Ok(update_daemon_set(fb, found_ds).marshal());
            }
        }
        return Err(());
    }

    fn state_after_create(fb: &FluentBit, obj: DynamicObject, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<KubeAPIRequest>), ()>) {
        let ds = DaemonSet::unmarshal(obj);
        if ds.is_ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }

    fn state_after_update(fb: &FluentBit, obj: DynamicObject, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<KubeAPIRequest>), ()>) {
        let ds = DaemonSet::unmarshal(obj);
        if ds.is_ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }
}

pub fn update_daemon_set(fb: &FluentBit, found_daemon_set: DaemonSet) -> (daemon_set: DaemonSet)
    requires
        fb@.well_formed(),
        found_daemon_set@.spec.is_Some(),
    ensures daemon_set@ == model_resource::update_daemon_set(fb@, found_daemon_set@),
{
    let made_ds = make_daemon_set(fb);

    let mut daemon_set = found_daemon_set.clone();
    daemon_set.set_metadata({
        let mut metadata = found_daemon_set.metadata();
        metadata.set_owner_references(make_owner_references(fb));
        metadata.unset_finalizers();
        metadata.set_labels(made_ds.metadata().labels().unwrap());
        metadata.set_annotations(made_ds.metadata().annotations().unwrap());
        metadata
    });
    daemon_set.set_spec({
        let mut ds_spec = found_daemon_set.spec().unwrap();
        let made_spec = made_ds.spec().unwrap();
        ds_spec.set_template(made_spec.template());
        ds_spec
    });
    daemon_set
}

pub fn make_daemon_set_name(fb: &FluentBit) -> (name: String)
    requires
        fb@.well_formed(),
    ensures name@ == model_resource::make_daemon_set_name(fb@),
{
    fb.metadata().name().unwrap()
}

pub fn make_daemon_set(fb: &FluentBit) -> (daemon_set: DaemonSet)
    requires
        fb@.well_formed(),
    ensures daemon_set@ == model_resource::make_daemon_set(fb@),
{
    let mut daemon_set = DaemonSet::default();
    daemon_set.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_daemon_set_name(fb));
        metadata.set_labels(make_labels(fb));
        metadata.set_annotations(fb.spec().annotations());
        metadata.set_owner_references(make_owner_references(fb));
        metadata
    });
    daemon_set.set_spec({
        let mut daemon_set_spec = DaemonSetSpec::default();
        // Set the selector used for querying pods of this daemon set
        daemon_set_spec.set_selector({
            let mut selector = LabelSelector::default();
            selector.set_match_labels(make_base_labels(fb));
            selector
        });
        // Set the template used for creating pods
        daemon_set_spec.set_template({
            let mut pod_template_spec = PodTemplateSpec::default();
            pod_template_spec.set_metadata({
                let mut metadata = ObjectMeta::default();
                metadata.set_labels(make_labels(fb));
                metadata.set_annotations(fb.spec().annotations());
                metadata
            });
            pod_template_spec.set_spec(make_fluentbit_pod_spec(fb));
            pod_template_spec
        });
        daemon_set_spec
    });
    daemon_set
}

#[verifier(spinoff_prover)]
fn make_fluentbit_pod_spec(fb: &FluentBit) -> (pod_spec: PodSpec)
    requires
        fb@.well_formed(),
    ensures pod_spec@ == model_resource::make_fluentbit_pod_spec(fb@),
{
    let mut pod_spec = PodSpec::default();
    pod_spec.set_service_account_name(fb.metadata().name().unwrap());
    if fb.spec().image_pull_secrets().is_some() {
        pod_spec.set_image_pull_secrets(fb.spec().image_pull_secrets().unwrap());
    }
    if fb.spec().init_containers().is_some() {
        pod_spec.set_init_containers(fb.spec().init_containers().unwrap());
    }
    pod_spec.set_containers({
        let mut containers = Vec::new();
        containers.push({
            let mut fb_container = Container::default();
            fb_container.set_name(new_strlit("fluent-bit").to_string());
            fb_container.set_image(fb.spec().image());
            if fb.spec().image_pull_policy().is_some() {
                fb_container.set_image_pull_policy(fb.spec().image_pull_policy().unwrap());
            }
            if fb.spec().env_vars().is_some() {
                fb_container.set_env({
                    let mut env = make_env(&fb);
                    let mut fb_env = fb.spec().env_vars().unwrap();
                    env.append(&mut fb_env);
                    proof {
                        assert_seqs_equal!(env@.map_values(|e: EnvVar| e@), model_resource::make_env(fb@) + fb@.spec.env_vars.get_Some_0());
                    }
                    env
                });
            } else {
                fb_container.set_env(make_env(&fb));
            }
            if fb.spec().liveness_probe().is_some() {
                fb_container.set_liveness_probe(fb.spec().liveness_probe().unwrap())
            }
            if fb.spec().readiness_probe().is_some() {
                fb_container.set_readiness_probe(fb.spec().readiness_probe().unwrap())
            }
            fb_container.set_volume_mounts({
                let mut volume_mounts = if fb.spec().volume_mounts().is_some() {
                        fb.spec().volume_mounts().unwrap()
                    } else {
                        Vec::new()
                    };
                volume_mounts.push({
                    let mut volume_mount = VolumeMount::default();
                    volume_mount.set_name(new_strlit("config").to_string());
                    volume_mount.set_read_only(true);
                    volume_mount.set_mount_path(new_strlit("/fluent-bit/config").to_string());
                    volume_mount
                });
                if !fb.spec().disable_log_volumes() {
                    volume_mounts.push({
                        let mut volume_mount = VolumeMount::default();
                        volume_mount.set_name(new_strlit("varlibcontainers").to_string());
                        volume_mount.set_read_only(true);
                        if fb.spec().container_log_real_path().is_some() {
                            volume_mount.set_mount_path(fb.spec().container_log_real_path().unwrap());
                        } else {
                            volume_mount.set_mount_path(new_strlit("/containers").to_string());
                        }
                        volume_mount.overwrite_mount_propagation(fb.spec().internal_mount_propagation());
                        volume_mount
                    });
                    volume_mounts.push({
                        let mut volume_mount = VolumeMount::default();
                        volume_mount.set_name(new_strlit("varlogs").to_string());
                        volume_mount.set_read_only(true);
                        volume_mount.set_mount_path(new_strlit("/var/log/").to_string());
                        volume_mount.overwrite_mount_propagation(fb.spec().internal_mount_propagation());
                        volume_mount
                    });
                    volume_mounts.push({
                        let mut volume_mount = VolumeMount::default();
                        volume_mount.set_name(new_strlit("systemd").to_string());
                        volume_mount.set_read_only(true);
                        volume_mount.set_mount_path(new_strlit("/var/log/journal").to_string());
                        volume_mount.overwrite_mount_propagation(fb.spec().internal_mount_propagation());
                        volume_mount
                    });
                }
                if fb.spec().position_db().is_some() {
                    volume_mounts.push({
                        let mut volume_mount = VolumeMount::default();
                        volume_mount.set_name(new_strlit("positions").to_string());
                        volume_mount.set_mount_path(new_strlit("/fluent-bit/tail").to_string());
                        volume_mount
                    });
                }
                proof {
                    assert_seqs_equal!(
                        volume_mounts@.map_values(|volume_mount: VolumeMount| volume_mount@),
                        model_resource::make_fluentbit_pod_spec(fb@).containers[0].volume_mounts.get_Some_0()
                    );
                }
                volume_mounts
            });
            fb_container.set_ports({
                let mut ports = if fb.spec().ports().is_some() {
                        fb.spec().ports().unwrap()
                    } else {
                        Vec::new()
                    };
                let metrics_port = if fb.spec().metrics_port().is_some() {
                    fb.spec().metrics_port().unwrap()
                } else {
                    2020
                };
                ports.push(ContainerPort::new_with(new_strlit("metrics").to_string(), metrics_port));
                proof {
                    assert_seqs_equal!(
                        ports@.map_values(|port: ContainerPort| port@),
                        model_resource::make_fluentbit_pod_spec(fb@).containers[0].ports.get_Some_0()
                    );
                }
                ports
            });
            fb_container.overwrite_resources(fb.spec().resources());
            if fb.spec().args().is_some() {
                fb_container.set_args(fb.spec().args().unwrap());
            }
            if fb.spec().command().is_some() {
                fb_container.set_command(fb.spec().command().unwrap());
            }
            if fb.spec().container_security_context().is_some() {
                fb_container.set_security_context(fb.spec().container_security_context().unwrap());
            }
            fb_container
        });
        proof {
            assert_seqs_equal!(
                containers@.map_values(|container: Container| container@),
                model_resource::make_fluentbit_pod_spec(fb@).containers
            );
        }
        containers
    });
    pod_spec.set_volumes({
        let mut volumes = if fb.spec().volumes().is_some() {
                fb.spec().volumes().unwrap()
            } else {
                Vec::new()
            };
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("config").to_string());
            volume.set_secret({
                let mut secret = SecretVolumeSource::default();
                secret.set_secret_name(fb.spec().fluentbit_config_name());
                secret
            });
            volume
        });
        if !fb.spec().disable_log_volumes() {
            volumes.push({
                let mut volume = Volume::default();
                volume.set_name(new_strlit("varlibcontainers").to_string());
                volume.set_host_path({
                    let mut host_path = HostPathVolumeSource::default();
                    if fb.spec().container_log_real_path().is_some() {
                        host_path.set_path(fb.spec().container_log_real_path().unwrap());
                    } else {
                        host_path.set_path(new_strlit("/containers").to_string());
                    }
                    host_path
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
        }
        if fb.spec().position_db().is_some() {
            volumes.push({
                let mut volume = Volume::default();
                volume.set_name(new_strlit("positions").to_string());
                volume.set_host_path(fb.spec().position_db().unwrap());
                volume
            });
        }

        proof {
            assert_seqs_equal!(
                volumes@.map_values(|vol: Volume| vol@),
                model_resource::make_fluentbit_pod_spec(fb@).volumes.get_Some_0()
            );
        }
        volumes
    });
    pod_spec.overwrite_tolerations(fb.spec().tolerations());
    pod_spec.overwrite_affinity(fb.spec().affinity());
    pod_spec.set_node_selector(fb.spec().node_selector());
    pod_spec.overwrite_runtime_class_name(fb.spec().runtime_class_name());
    pod_spec.overwrite_dns_policy(fb.spec().dns_policy());
    pod_spec.overwrite_priority_class_name(fb.spec().priority_class_name());
    pod_spec.overwrite_scheduler_name(fb.spec().scheduler_name());
    if fb.spec().security_context().is_some() {
        pod_spec.set_security_context(fb.spec().security_context().unwrap());
    }
    if fb.spec().host_network().is_some() {
        pod_spec.set_host_network(fb.spec().host_network().unwrap());
    }
    pod_spec
}

fn make_env(fb: &FluentBit) -> (env_vars: Vec<EnvVar>)
    ensures env_vars@.map_values(|v: EnvVar| v@) == model_resource::make_env(fb@),
{
    let mut env_vars = Vec::new();
    env_vars.push(EnvVar::new_with(
        new_strlit("NODE_NAME").to_string(), None, Some(EnvVarSource::new_with_field_ref({
            let mut selector = ObjectFieldSelector::default();
            selector.set_field_path(new_strlit("spec.nodeName").to_string());
            selector
        }))
    ));
    env_vars.push(EnvVar::new_with(
        new_strlit("HOST_IP").to_string(), None, Some(EnvVarSource::new_with_field_ref({
            let mut selector = ObjectFieldSelector::default();
            selector.set_field_path(new_strlit("status.hostIP").to_string());
            selector
        }))
    ));
    proof {
        assert_seqs_equal!(env_vars@.map_values(|v: EnvVar| v@), model_resource::make_env(fb@));
    }
    env_vars
}

}
