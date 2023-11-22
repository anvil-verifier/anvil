// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::rabbitmq_controller::model::resource as model_resource;
use crate::rabbitmq_controller::trusted::exec_types::*;
use crate::rabbitmq_controller::trusted::spec_types::RabbitmqClusterView;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct StatefulSetBuilder {}

impl ResourceBuilder<RabbitmqCluster, RabbitmqReconcileState, model_resource::StatefulSetBuilder> for StatefulSetBuilder {
    open spec fn requirements(rabbitmq: RabbitmqClusterView) -> bool { rabbitmq.well_formed() }

    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: StatefulSet::api_resource(),
            name: make_stateful_set_name(rabbitmq),
            namespace: rabbitmq.metadata().namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, ()> {
        if state.latest_config_map_rv_opt.is_some() {
            Ok(make_stateful_set(rabbitmq, state.latest_config_map_rv_opt.as_ref().unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        // We check the owner reference of the found stateful set here to ensure that it is not created from
        // previously existing (and now deleted) cr. Otherwise, if the replicas of the current cr is smaller
        // than the previous one, scaling down, which should be prohibited, will happen.
        // If the found stateful set doesn't contain the controller owner reference of the current cr, we will
        // just let the reconciler enter the error state and wait for the garbage collector to delete it. So
        // after that, when a new round of reconcile starts, there is no stateful set in etcd, the reconciler
        // will go to create a new one.
        let sts = StatefulSet::unmarshal(obj);
        if sts.is_ok() {
            let found_sts = sts.unwrap();
            if found_sts.metadata().owner_references_only_contains(rabbitmq.controller_owner_ref())
            && state.latest_config_map_rv_opt.is_some() && found_sts.spec().is_some() {
                return Ok(update_stateful_set(rabbitmq, found_sts, state.latest_config_map_rv_opt.as_ref().unwrap()).marshal());
            }
        }
        return Err(());
    }

    fn state_after_create(rabbitmq: &RabbitmqCluster, obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<KubeAPIRequest>), ()>) {
        let sts = StatefulSet::unmarshal(obj);
        if sts.is_ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }

    fn state_after_update(rabbitmq: &RabbitmqCluster, obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<KubeAPIRequest>), ()>) {
        let sts = StatefulSet::unmarshal(obj);
        if sts.is_ok() {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }
}

pub fn update_stateful_set(rabbitmq: &RabbitmqCluster, found_stateful_set: StatefulSet, config_map_rv: &String) -> (stateful_set: StatefulSet)
    requires
        rabbitmq@.well_formed(),
        rabbitmq@.metadata.namespace.is_Some(),
        found_stateful_set@.spec.is_Some(),
    ensures stateful_set@ == model_resource::update_stateful_set(rabbitmq@, found_stateful_set@, config_map_rv@),
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

pub fn sts_restart_annotation() -> (anno: String)
    ensures anno@ == model_resource::sts_restart_annotation(),
{
    new_strlit("anvil.dev/lastRestartAt").to_string()
}

pub fn make_stateful_set_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires
        rabbitmq@.well_formed(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures name@ == model_resource::make_stateful_set_name(rabbitmq@),
{
    rabbitmq.metadata().name().unwrap().concat(new_strlit("-server"))
}

pub fn make_stateful_set(rabbitmq: &RabbitmqCluster, config_map_rv: &String) -> (stateful_set: StatefulSet)
    requires
        rabbitmq@.well_formed(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures stateful_set@ == model_resource::make_stateful_set(rabbitmq@, config_map_rv@),
{
    let mut stateful_set = StatefulSet::default();
    stateful_set.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_stateful_set_name(rabbitmq));
        metadata.set_namespace(rabbitmq.metadata().namespace().unwrap());
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
        stateful_set_spec.set_service_name(rabbitmq.metadata().name().unwrap().concat(new_strlit("-nodes")));
        // Set the selector used for querying pods of this stateful set
        stateful_set_spec.set_selector({
            let mut selector = LabelSelector::default();
            selector.set_match_labels({
                let mut match_labels = StringMap::empty();
                match_labels.insert(new_strlit("app").to_string(), rabbitmq.metadata().name().unwrap());
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
                        model_resource::make_stateful_set(rabbitmq@, config_map_rv@).spec.get_Some_0().volume_claim_templates.get_Some_0()
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
                        metadata.set_namespace(rabbitmq.metadata().namespace().unwrap());
                        metadata.set_labels({
                            let mut labels = StringMap::empty();
                            labels.insert(new_strlit("app").to_string(), rabbitmq.metadata().name().unwrap());
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
                                    model_resource::make_stateful_set(rabbitmq@, config_map_rv@)
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
                        pvc_spec.set_storage_class_name(rabbitmq.spec().persistence().storage_class_name());
                        pvc_spec
                    });
                    pvc
                });
                proof {
                    assert_seqs_equal!(
                        volume_claim_templates@.map_values(|pvc: PersistentVolumeClaim| pvc@),
                        model_resource::make_stateful_set(rabbitmq@, config_map_rv@).spec.get_Some_0().volume_claim_templates.get_Some_0()
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
        stateful_set_spec.set_pod_management_policy(rabbitmq.spec().pod_management_policy());

        if rabbitmq.spec().persistent_volume_claim_retention_policy().is_some() {
            stateful_set_spec.set_pvc_retention_policy(rabbitmq.spec().persistent_volume_claim_retention_policy().unwrap());
        }
        stateful_set_spec
    });
    stateful_set
}

pub fn make_rabbitmq_pod_spec(rabbitmq: &RabbitmqCluster) -> (pod_spec: PodSpec)
    requires
        rabbitmq@.well_formed(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures pod_spec@ == model_resource::make_rabbitmq_pod_spec(rabbitmq@),
{
    let mut volumes = Vec::new();
    volumes.push({
        let mut volume = Volume::default();
        volume.set_name(new_strlit("plugins-conf").to_string());
        volume.set_config_map({
            let mut config_map = ConfigMapVolumeSource::default();
            config_map.set_name(rabbitmq.metadata().name().unwrap().concat(new_strlit("-plugins-conf")));
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
                        config_map.set_name(rabbitmq.metadata().name().unwrap().concat(new_strlit("-server-conf")));
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
                                    model_resource::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()[1].projected.get_Some_0()
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
                        secret.set_name(rabbitmq.metadata().name().unwrap().concat(new_strlit("-default-user")));
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
                                    model_resource::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()[1].projected.get_Some_0()
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
                        model_resource::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()[1].projected.get_Some_0()
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
            secret.set_secret_name(rabbitmq.metadata().name().unwrap().concat(new_strlit("-erlang-cookie")));
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
                        model_resource::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()[5].downward_api.get_Some_0().items.get_Some_0()
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
            model_resource::make_rabbitmq_pod_spec(rabbitmq@).volumes.get_Some_0()
        );
    }
    let mut pod_spec = PodSpec::default();
    pod_spec.set_service_account_name(rabbitmq.metadata().name().unwrap().concat(new_strlit("-server")));
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

                proof{
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
                    volume_mount.set_mount_path(new_strlit("/tmp/default_user.conf").to_string());
                    volume_mount.set_sub_path(new_strlit("default_user.conf").to_string());
                    volume_mount
                });

                proof {
                    assert_seqs_equal!(
                        volume_mounts@.map_values(|volume_mount: VolumeMount| volume_mount@),
                        model_resource::make_rabbitmq_pod_spec(rabbitmq@).init_containers.unwrap()[0].volume_mounts.get_Some_0()
                    );
                }
                volume_mounts
            });
            rabbitmq_container
        });
        proof {
            assert_seqs_equal!(
                containers@.map_values(|container: Container| container@),
                model_resource::make_rabbitmq_pod_spec(rabbitmq@).init_containers.unwrap()
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
            rabbitmq_container.set_lifecycle({
                let mut lifecycle = Lifecycle::default();
                lifecycle.set_pre_stop({
                    let mut pre_stop = LifecycleHandler::default();
                    pre_stop.set_exec({
                        let mut exec = ExecAction::default();
                        exec.set_command({
                            let mut command = Vec::new();
                            command.push(new_strlit("/bin/bash").to_string());
                            command.push(new_strlit("-c").to_string());
                            command.push(new_strlit("if [ ! -z \"$(cat /etc/pod-info/skipPreStopChecks)\" ]; then exit 0; fi; \
                                rabbitmq-upgrade await_online_quorum_plus_one -t 604800; \
                                rabbitmq-upgrade await_online_synchronized_mirror -t 604800; \
                                rabbitmq-upgrade drain -t 604800"
                            ).to_string());

                            proof {
                                assert_seqs_equal!(
                                    command@.map_values(|s: String| s@),
                                    model_resource::make_rabbitmq_pod_spec(rabbitmq@).containers[0].lifecycle.get_Some_0().pre_stop.get_Some_0().exec_.get_Some_0().command.get_Some_0()
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

                if rabbitmq.spec().rabbitmq_config().is_some() && rabbitmq.spec().rabbitmq_config().unwrap().env_config().is_some()
                && !rabbitmq.spec().rabbitmq_config().unwrap().env_config().unwrap().eq(&new_strlit("").to_string()) {
                    volume_mounts.push({
                        let mut volume_mount = VolumeMount::default();
                        volume_mount.set_name(new_strlit("server-conf").to_string());
                        volume_mount.set_mount_path(new_strlit("/etc/rabbitmq/rabbitmq-env.conf").to_string());
                        volume_mount.set_sub_path(new_strlit("rabbitmq-env.conf").to_string());
                        volume_mount
                    });
                }

                if rabbitmq.spec().rabbitmq_config().is_some() && rabbitmq.spec().rabbitmq_config().unwrap().advanced_config().is_some()
                && !rabbitmq.spec().rabbitmq_config().unwrap().advanced_config().unwrap().eq(&new_strlit("").to_string()) {
                    volume_mounts.push({
                        let mut volume_mount = VolumeMount::default();
                        volume_mount.set_name(new_strlit("server-conf").to_string());
                        volume_mount.set_mount_path(new_strlit("/etc/rabbitmq/advanced.config").to_string());
                        volume_mount.set_sub_path(new_strlit("advanced.config").to_string());
                        volume_mount
                    });
                }

                proof {
                    assert_seqs_equal!(
                        volume_mounts@.map_values(|volume_mount: VolumeMount| volume_mount@),
                        model_resource::make_rabbitmq_pod_spec(rabbitmq@).containers[0].volume_mounts.get_Some_0()
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
                        model_resource::make_rabbitmq_pod_spec(rabbitmq@).containers[0].ports.get_Some_0()
                    );
                }

                ports
            });
            rabbitmq_container.set_readiness_probe({
                let mut probe = Probe::default();
                probe.set_failure_threshold(3);
                probe.set_initial_delay_seconds(10);
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
                model_resource::make_rabbitmq_pod_spec(rabbitmq@).containers
            );
        }
        containers
    });
    pod_spec.set_volumes(volumes);
    pod_spec.overwrite_affinity(rabbitmq.spec().affinity());
    pod_spec.overwrite_tolerations(rabbitmq.spec().tolerations());
    pod_spec.set_termination_grace_period_seconds(604800);
    pod_spec
}

pub fn make_env_vars(rabbitmq: &RabbitmqCluster) -> (env_vars: Vec<EnvVar>)
    requires rabbitmq@.well_formed(),
    ensures env_vars@.map_values(|v: EnvVar| v@) == model_resource::make_env_vars(rabbitmq@)
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
        new_strlit("K8S_SERVICE_NAME").to_string(), Some(rabbitmq.metadata().name().unwrap().concat(new_strlit("-nodes"))), None
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
            model_resource::make_env_vars(rabbitmq@)
        );
    }
    env_vars
}

}
