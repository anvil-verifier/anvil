// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::exec::types::*;
use crate::fluent_controller::fluentbit::spec::resource as spec_resource;
use crate::fluent_controller::fluentbit::spec::types::FluentBitView;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
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

impl ResourceBuilder<FluentBit, FluentBitReconcileState, spec_resource::DaemonSetBuilder> for DaemonSetBuilder {
    open spec fn requirements(fb: FluentBitView) -> bool {
        &&& fb.well_formed()
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

    fn state_after_create_or_update(obj: DynamicObject, state: FluentBitReconcileState) -> (res: Result<FluentBitReconcileState, ()>) {
        let ds = DaemonSet::unmarshal(obj);
        if ds.is_ok() {
            Ok(state)
        } else {
            Err(())
        }
    }
}

pub fn update_daemon_set(fb: &FluentBit, found_daemon_set: DaemonSet) -> (daemon_set: DaemonSet)
    requires
        fb@.well_formed(),
        found_daemon_set@.spec.is_Some(),
    ensures
        daemon_set@ == spec_resource::update_daemon_set(fb@, found_daemon_set@),
{
    let made_ds = make_daemon_set(fb);

    let mut daemon_set = found_daemon_set.clone();
    daemon_set.set_spec({
        let mut ds_spec = found_daemon_set.spec().unwrap();
        let made_spec = made_ds.spec().unwrap();
        ds_spec.set_template(made_spec.template());
        ds_spec
    });
    daemon_set.set_metadata({
        let mut metadata = found_daemon_set.metadata();
        metadata.set_owner_references(make_owner_references(fb));
        metadata.unset_finalizers();
        metadata.set_labels(made_ds.metadata().labels().unwrap());
        metadata.set_annotations(made_ds.metadata().annotations().unwrap());
        metadata
    });
    daemon_set
}

pub fn make_daemon_set_name(fb: &FluentBit) -> (name: String)
    requires
        fb@.well_formed(),
    ensures
        name@ == spec_resource::make_daemon_set_name(fb@),
{
    fb.metadata().name().unwrap()
}

pub fn make_daemon_set(fb: &FluentBit) -> (daemon_set: DaemonSet)
    requires
        fb@.well_formed(),
    ensures
        daemon_set@ == spec_resource::make_daemon_set(fb@),
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

fn make_fluentbit_pod_spec(fb: &FluentBit) -> (pod_spec: PodSpec)
    requires
        fb@.well_formed(),
    ensures
        pod_spec@ == spec_resource::make_fluentbit_pod_spec(fb@),
{
    let mut pod_spec = PodSpec::default();
    pod_spec.set_service_account_name(fb.metadata().name().unwrap());
    pod_spec.set_containers({
        let mut containers = Vec::new();
        containers.push({
            let mut fb_container = Container::default();
            fb_container.set_name(new_strlit("fluent-bit").to_string());
            fb_container.set_image(new_strlit("kubesphere/fluent-bit:v2.1.7").to_string());
            fb_container.set_env(make_env(&fb));
            fb_container.set_volume_mounts({
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
                        spec_resource::make_fluentbit_pod_spec(fb@).containers[0].volume_mounts.get_Some_0()
                    );
                }
                volume_mounts
            });
            fb_container.set_ports({
                let mut ports = Vec::new();
                ports.push(ContainerPort::new_with(new_strlit("metrics").to_string(), 2020));
                proof {
                    assert_seqs_equal!(
                        ports@.map_values(|port: ContainerPort| port@),
                        spec_resource::make_fluentbit_pod_spec(fb@).containers[0].ports.get_Some_0()
                    );
                }
                ports
            });
            fb_container.overwrite_resources(fb.spec().resources());
            fb_container
        });
        proof {
            assert_seqs_equal!(
                containers@.map_values(|container: Container| container@),
                spec_resource::make_fluentbit_pod_spec(fb@).containers
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
                secret.set_secret_name(fb.spec().fluentbit_config_name());
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
                spec_resource::make_fluentbit_pod_spec(fb@).volumes.get_Some_0()
            );
        }
        volumes
    });
    pod_spec.overwrite_tolerations(fb.spec().tolerations());
    pod_spec
}

fn make_env(fb: &FluentBit) -> (env_vars: Vec<EnvVar>)
    ensures
        env_vars@.map_values(|v: EnvVar| v@) == spec_resource::make_env(fb@),
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
        assert_seqs_equal!(
            env_vars@.map_values(|v: EnvVar| v@),
            spec_resource::make_env(fb@),
        );
    }
    env_vars
}


}
