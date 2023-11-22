// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use crate::zookeeper_controller::exec::resource::common::*;
use crate::zookeeper_controller::model::resource as model_resource;
use crate::zookeeper_controller::trusted::{
    exec_types::*, spec_types::ZookeeperClusterView, step::*,
};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct StatefulSetBuilder {}

impl ResourceBuilder<ZookeeperCluster, ZookeeperReconcileState, model_resource::StatefulSetBuilder> for StatefulSetBuilder {
    open spec fn requirements(zk: ZookeeperClusterView) -> bool { zk.well_formed() }

    fn get_request(zk: &ZookeeperCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: StatefulSet::api_resource(),
            name: make_stateful_set_name(zk),
            namespace: zk.metadata().namespace().unwrap(),
        }
    }

    fn make(zk: &ZookeeperCluster, state: &ZookeeperReconcileState) -> Result<DynamicObject, ()> {
        if state.latest_config_map_rv_opt.is_some() {
            Ok(make_stateful_set(zk, state.latest_config_map_rv_opt.as_ref().unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn update(zk: &ZookeeperCluster, state: &ZookeeperReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        // Only proceed if the stateful set is owned by the current cr
        // so that we won't accidentally update ports or some other mutable fields.
        let sts = StatefulSet::unmarshal(obj);
        if sts.is_ok() {
            let found_sts = sts.unwrap();
            if found_sts.metadata().owner_references_only_contains(zk.controller_owner_ref())
            && state.latest_config_map_rv_opt.is_some() && found_sts.spec().is_some() {
                return Ok(update_stateful_set(zk, &found_sts, state.latest_config_map_rv_opt.as_ref().unwrap()).marshal());
            }
        }
        return Err(());
    }

    fn state_after_create(zk: &ZookeeperCluster, obj: DynamicObject, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<KubeAPIRequest>), ()>) {
        let sts_obj = StatefulSet::unmarshal(obj);
        if sts_obj.is_ok() {
            let updated_zk = update_zk_status(zk, 0);
            let req = KubeAPIRequest::UpdateStatusRequest(KubeUpdateStatusRequest {
                api_resource: ZookeeperCluster::api_resource(),
                name: zk.metadata().name().unwrap(),
                namespace: zk.metadata().namespace().unwrap(),
                obj: updated_zk.marshal(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterUpdateStatus,
                ..state
            };
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    fn state_after_update(zk: &ZookeeperCluster, obj: DynamicObject, state: ZookeeperReconcileState) -> (res: Result<(ZookeeperReconcileState, Option<KubeAPIRequest>), ()>) {
        let sts_obj = StatefulSet::unmarshal(obj);
        if sts_obj.is_ok() {
            let stateful_set = sts_obj.unwrap();
            let ready_replicas = if stateful_set.status().is_some() && stateful_set.status().as_ref().unwrap().ready_replicas().is_some() {
                stateful_set.status().as_ref().unwrap().ready_replicas().unwrap()
            } else {
                0
            };
            let updated_zk = update_zk_status(zk, ready_replicas);
            let req = KubeAPIRequest::UpdateStatusRequest(KubeUpdateStatusRequest {
                api_resource: ZookeeperCluster::api_resource(),
                name: zk.metadata().name().unwrap(),
                namespace: zk.metadata().namespace().unwrap(),
                obj: updated_zk.marshal(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterUpdateStatus,
                ..state
            };
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub fn make_stateful_set_name(zk: &ZookeeperCluster) -> (name: String)
    requires zk@.well_formed(),
    ensures name@ == model_resource::make_stateful_set_name(zk@),
{
    zk.metadata().name().unwrap()
}

pub fn update_stateful_set(zk: &ZookeeperCluster, found_stateful_set: &StatefulSet, rv: &String) -> (stateful_set: StatefulSet)
    requires
        zk@.well_formed(),
        found_stateful_set@.spec.is_Some(),
    ensures stateful_set@ == model_resource::update_stateful_set(zk@, found_stateful_set@, rv@),
{
    let mut stateful_set = found_stateful_set.clone();
    let made_stateful_set = make_stateful_set(zk, rv);
    stateful_set.set_metadata({
        let mut metadata = found_stateful_set.metadata();
        metadata.set_owner_references(make_owner_references(zk));
        metadata.unset_finalizers();
        metadata.set_labels(made_stateful_set.metadata().labels().unwrap());
        metadata.set_annotations(made_stateful_set.metadata().annotations().unwrap());
        metadata
    });
    stateful_set.set_spec({
        let mut spec = found_stateful_set.spec().unwrap();
        spec.set_replicas(made_stateful_set.spec().unwrap().replicas().unwrap());
        spec.set_template(made_stateful_set.spec().unwrap().template());
        spec.set_pvc_retention_policy(made_stateful_set.spec().unwrap().persistent_volume_claim_retention_policy().unwrap());
        spec
    });
    stateful_set
}

/// The StatefulSet manages the zookeeper server containers (as Pods)
/// and the volumes attached to each server (as PersistentVolumeClaims)
pub fn make_stateful_set(zk: &ZookeeperCluster, rv: &String) -> (stateful_set: StatefulSet)
    requires zk@.well_formed(),
    ensures stateful_set@ == model_resource::make_stateful_set(zk@, rv@),
{
    let mut stateful_set = StatefulSet::default();
    stateful_set.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_stateful_set_name(zk));
        metadata.set_labels(make_labels(zk));
        metadata.set_annotations(zk.spec().annotations());
        metadata.set_owner_references(make_owner_references(zk));
        metadata
    });
    stateful_set.set_spec({
        let mut stateful_set_spec = StatefulSetSpec::default();
        // Set the replica number
        stateful_set_spec.set_replicas(zk.spec().replicas());
        // Set the headless service to assign DNS entry to each zookeeper server
        stateful_set_spec.set_service_name(zk.metadata().name().unwrap().concat(new_strlit("-headless")));
        // Set the selector used for querying pods of this stateful set
        stateful_set_spec.set_selector({
            let mut selector = LabelSelector::default();
            selector.set_match_labels(make_base_labels(zk));
            selector
        });
        stateful_set_spec.set_pvc_retention_policy({
            let mut policy = StatefulSetPersistentVolumeClaimRetentionPolicy::default();
            policy.set_when_deleted(new_strlit("Delete").to_string());
            policy.set_when_scaled(new_strlit("Delete").to_string());
            policy
        });
        // Set the template used for creating pods
        stateful_set_spec.set_template({
            let mut pod_template_spec = PodTemplateSpec::default();
            pod_template_spec.set_metadata({
                let mut metadata = ObjectMeta::default();
                metadata.set_labels(make_labels(zk));
                metadata.set_annotations({
                    let mut annotations = zk.spec().annotations();
                    annotations.insert(new_strlit("anvil.dev/lastRestartAt").to_string(), rv.clone());
                    annotations
                });
                metadata
            });
            pod_template_spec.set_spec(make_zk_pod_spec(zk));
            pod_template_spec
        });
        // Set the templates used for creating the persistent volume claims attached to each pod
        stateful_set_spec.set_volume_claim_templates({
            if zk.spec().persistence().enabled() {
                let mut volume_claim_templates = Vec::new();
                volume_claim_templates.push({
                    let mut pvc = PersistentVolumeClaim::default();
                    pvc.set_metadata({
                        let mut metadata = ObjectMeta::default();
                        metadata.set_name(new_strlit("data").to_string());
                        metadata.set_labels(make_base_labels(zk));
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
                                    model_resource::make_stateful_set(zk@, rv@)
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
                                requests.insert(new_strlit("storage").to_string(), zk.spec().persistence().storage_size());
                                requests
                            });
                            resources
                        });
                        pvc_spec.set_storage_class_name(zk.spec().persistence().storage_class_name());
                        pvc_spec
                    });
                    pvc
                });
                proof {
                    assert_seqs_equal!(
                        volume_claim_templates@.map_values(|pvc: PersistentVolumeClaim| pvc@),
                        model_resource::make_stateful_set(zk@, rv@).spec.get_Some_0().volume_claim_templates.get_Some_0()
                    );
                }
                volume_claim_templates
            } else {
                let empty_templates = Vec::<PersistentVolumeClaim>::new();
                proof {
                    assert_seqs_equal!(
                        empty_templates@.map_values(|pvc: PersistentVolumeClaim| pvc@),
                        model_resource::make_stateful_set(zk@, rv@).spec.get_Some_0().volume_claim_templates.get_Some_0()
                    );
                }
                empty_templates
            }
        });
        stateful_set_spec
    });
    stateful_set
}

pub fn make_zk_pod_spec(zk: &ZookeeperCluster) -> (pod_spec: PodSpec)
    requires zk@.well_formed(),
    ensures pod_spec@ == model_resource::make_zk_pod_spec(zk@),
{
    let mut pod_spec = PodSpec::default();

    pod_spec.overwrite_affinity(zk.spec().affinity());
    pod_spec.set_containers({
        let mut containers = Vec::new();
        containers.push({
            let mut zk_container = Container::default();
            zk_container.set_name(new_strlit("zookeeper").to_string());
            zk_container.set_image(zk.spec().image());
            zk_container.set_command({
                let mut command = Vec::new();
                command.push(new_strlit("/usr/local/bin/zookeeperStart.sh").to_string());
                proof {
                    let spec_cmd = seq![new_strlit("/usr/local/bin/zookeeperStart.sh")@];
                    assert_seqs_equal!(command@.map_values(|s: String| s@), spec_cmd);
                }
                command
            });
            zk_container.set_lifecycle({
                let mut lifecycle = Lifecycle::default();
                lifecycle.set_pre_stop({
                    let mut pre_stop = LifecycleHandler::default();
                    pre_stop.set_exec({
                        let mut exec = ExecAction::default();
                        exec.set_command({
                            let mut command = Vec::new();
                            command.push(new_strlit("zookeeperTeardown.sh").to_string());

                            proof {
                                assert_seqs_equal!(
                                    command@.map_values(|s: String| s@),
                                    model_resource::make_zk_pod_spec(zk@).containers[0].lifecycle.get_Some_0().pre_stop.get_Some_0().exec_.get_Some_0().command.get_Some_0()
                                );
                            }

                            command
                        });
                        exec
                    });
                    pre_stop
                });
                lifecycle
            });
            zk_container.set_image_pull_policy(new_strlit("Always").to_string());
            zk_container.overwrite_resources(zk.spec().resources());
            zk_container.set_volume_mounts({
                let mut volume_mounts = Vec::new();
                volume_mounts.push({
                    let mut data_volume_mount = VolumeMount::default();
                    data_volume_mount.set_name(new_strlit("data").to_string());
                    data_volume_mount.set_mount_path(new_strlit("/data").to_string());
                    data_volume_mount
                });
                volume_mounts.push({
                    let mut conf_volume_mount = VolumeMount::default();
                    conf_volume_mount.set_name(new_strlit("conf").to_string());
                    conf_volume_mount.set_mount_path(new_strlit("/conf").to_string());
                    conf_volume_mount
                });

                proof {
                    assert_seqs_equal!(
                        volume_mounts@.map_values(|volume_mount: VolumeMount| volume_mount@),
                        model_resource::make_zk_pod_spec(zk@).containers[0].volume_mounts.get_Some_0()
                    );
                }

                volume_mounts
            });
            zk_container.set_ports({
                let mut ports = Vec::new();
                ports.push(ContainerPort::new_with(new_strlit("client").to_string(), zk.spec().ports().client()));
                ports.push(ContainerPort::new_with(new_strlit("quorum").to_string(), zk.spec().ports().quorum()));
                ports.push(ContainerPort::new_with(new_strlit("leader-election").to_string(), zk.spec().ports().leader_election()));
                ports.push(ContainerPort::new_with(new_strlit("metrics").to_string(), zk.spec().ports().metrics()));
                ports.push(ContainerPort::new_with(new_strlit("admin-server").to_string(), zk.spec().ports().admin_server()));

                proof {
                    assert_seqs_equal!(
                        ports@.map_values(|port: ContainerPort| port@),
                        model_resource::make_zk_pod_spec(zk@).containers[0].ports.get_Some_0()
                    );
                }

                ports
            });
            zk_container.set_readiness_probe({
                let mut probe = Probe::default();
                probe.set_exec({
                    let mut exec = ExecAction::default();
                    exec.set_command({
                        let mut command = Vec::new();
                        command.push(new_strlit("zookeeperReady.sh").to_string());

                        proof {
                            assert_seqs_equal!(
                                command@.map_values(|s: String| s@),
                                model_resource::make_zk_pod_spec(zk@).containers[0].readiness_probe.get_Some_0().exec_.get_Some_0().command.get_Some_0()
                            );
                        }

                        command
                    });
                    exec
                });
                probe.set_failure_threshold(3);
                probe.set_initial_delay_seconds(10);
                probe.set_period_seconds(10);
                probe.set_success_threshold(1);
                probe.set_timeout_seconds(10);
                probe
            });
            zk_container.set_liveness_probe({
                let mut probe = Probe::default();
                probe.set_exec({
                    let mut exec = ExecAction::default();
                    exec.set_command({
                        let mut command = Vec::new();
                        command.push(new_strlit("zookeeperLive.sh").to_string());

                        proof {
                            assert_seqs_equal!(
                                command@.map_values(|s: String| s@),
                                model_resource::make_zk_pod_spec(zk@).containers[0].liveness_probe.get_Some_0().exec_.get_Some_0().command.get_Some_0()
                            );
                        }

                        command
                    });
                    exec
                });
                probe.set_failure_threshold(3);
                probe.set_initial_delay_seconds(10);
                probe.set_period_seconds(10);
                probe.set_success_threshold(1);
                probe.set_timeout_seconds(10);
                probe
            });
            zk_container
        });

        proof {
            assert_seqs_equal!(
                containers@.map_values(|container: Container| container@),
                model_resource::make_zk_pod_spec(zk@).containers
            );
        }

        containers
    });
    pod_spec.set_volumes({
        let mut volumes = Vec::new();
        volumes.push({
            let mut volume = Volume::default();
            volume.set_name(new_strlit("conf").to_string());
            volume.set_config_map({
                let mut config_map = ConfigMapVolumeSource::default();
                config_map.set_name(zk.metadata().name().unwrap().concat(new_strlit("-configmap")));
                config_map
            });
            volume
        });
        if !zk.spec().persistence().enabled() {
            volumes.push({
                let mut volume = Volume::default();
                volume.set_name(new_strlit("data").to_string());
                volume.set_empty_dir(EmptyDirVolumeSource::default());
                volume
            });
        }

        proof {
            assert_seqs_equal!(
                volumes@.map_values(|vol: Volume| vol@),
                model_resource::make_zk_pod_spec(zk@).volumes.get_Some_0()
            );
        }

        volumes
    });
    pod_spec.overwrite_tolerations(zk.spec().tolerations());
    pod_spec.set_node_selector(zk.spec().node_selector());

    pod_spec
}

pub fn update_zk_status(zk: &ZookeeperCluster, ready_replicas: i32) -> (updated_zk: ZookeeperCluster)
    ensures updated_zk@ == model_resource::update_zk_status(zk@, ready_replicas as int),
{
    let mut updated_zk = zk.clone();
    updated_zk.set_status({
        let mut status = ZookeeperClusterStatus::default();
        status.set_ready_replicas(ready_replicas);
        status
    });
    updated_zk
}

}
