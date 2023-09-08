// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, container::*, error::*, label_selector::*,
    object_meta::*, owner_reference::*, persistent_volume_claim::*, pod::*, pod_template_spec::*,
    resource::*, resource_requirements::*, service::*, stateful_set::*, volume::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::{string_view::*, to_view::*};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::exec::{types::*, zookeeper_api::*};
use crate::zookeeper_controller::spec::reconciler as zk_spec;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;
use vstd::view::*;

verus! {

/// ZookeeperReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct ZookeeperReconcileState {
    // reconcile_step, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_step: ZookeeperReconcileStep,
    pub found_stateful_set_opt: Option<StatefulSet>,
    pub latest_config_map_rv_opt: Option<String>,
}

impl ZookeeperReconcileState {
    pub open spec fn to_view(&self) -> zk_spec::ZookeeperReconcileState {
        zk_spec::ZookeeperReconcileState {
            reconcile_step: self.reconcile_step,
            found_stateful_set_opt: match &self.found_stateful_set_opt {
                Some(sts) => Some(sts@),
                None => None,
            },
            latest_config_map_rv_opt: match &self.latest_config_map_rv_opt {
                Some(s) => Some(s@),
                None => None,
            },
        }
    }
}

pub struct ZookeeperReconciler {}

#[verifier(external)]
impl Reconciler<ZookeeperCluster, ZookeeperReconcileState, ZKAPIInput, ZKAPIOutput, ZKAPIShimLayer> for ZookeeperReconciler {
    fn reconcile_init_state(&self) -> ZookeeperReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(
        &self, zk: &ZookeeperCluster, resp_o: Option<Response<ZKAPIOutput>>, state: ZookeeperReconcileState
    ) -> (ZookeeperReconcileState, Option<Request<ZKAPIInput>>) {
        reconcile_core(zk, resp_o, state)
    }

    fn reconcile_done(&self, state: &ZookeeperReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(&self, state: &ZookeeperReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for ZookeeperReconciler {
    fn default() -> ZookeeperReconciler { ZookeeperReconciler{} }
}

pub fn reconcile_init_state() -> (state: ZookeeperReconcileState)
    ensures
        state.to_view() == zk_spec::reconcile_init_state(),
{
    ZookeeperReconcileState {
        reconcile_step: ZookeeperReconcileStep::Init,
        found_stateful_set_opt: None,
        latest_config_map_rv_opt: None,
    }
}

pub fn reconcile_done(state: &ZookeeperReconcileState) -> (res: bool)
    ensures
        res == zk_spec::reconcile_done(state.to_view()),
{
    match state.reconcile_step {
        ZookeeperReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &ZookeeperReconcileState) -> (res: bool)
    ensures
        res == zk_spec::reconcile_error(state.to_view()),
{
    match state.reconcile_step {
        ZookeeperReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(
    zk: &ZookeeperCluster, resp_o: Option<Response<ZKAPIOutput>>, state: ZookeeperReconcileState
) -> (res: (ZookeeperReconcileState, Option<Request<ZKAPIInput>>))
    requires
        zk@.well_formed(),
    ensures
        (res.0.to_view(), opt_request_to_view(&res.1)) == zk_spec::reconcile_core(zk@, opt_response_to_view(&resp_o), state.to_view()),
{
    let step = state.reconcile_step;
    match step {
        ZookeeperReconcileStep::Init => {
            let headless_service = make_headless_service(&zk);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: Service::api_resource(),
                namespace: zk.metadata().namespace().unwrap(),
                obj: headless_service.to_dynamic_object(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateHeadlessService,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        ZookeeperReconcileStep::AfterCreateHeadlessService => {
            let client_service = make_client_service(zk);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: Service::api_resource(),
                namespace: zk.metadata().namespace().unwrap(),
                obj: client_service.to_dynamic_object(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateClientService,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        ZookeeperReconcileStep::AfterCreateClientService => {
            let admin_server_service = make_admin_server_service(zk);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: Service::api_resource(),
                namespace: zk.metadata().namespace().unwrap(),
                obj: admin_server_service.to_dynamic_object(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterCreateAdminServerService,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        ZookeeperReconcileStep::AfterCreateAdminServerService => {
            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: ConfigMap::api_resource(),
                name: make_config_map_name(zk),
                namespace: zk.metadata().namespace().unwrap(),
            });
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::AfterGetConfigMap,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req_o)));
        },
        ZookeeperReconcileStep::AfterGetConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_cm_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_cm_resp.is_ok() {
                    let get_cm_result = ConfigMap::from_dynamic_object(get_cm_resp.unwrap());
                    if get_cm_result.is_ok() {
                        // Update the config map with the new configuration data
                        let found_config_map = get_cm_result.unwrap();
                        let new_config_map = update_config_map(zk, &found_config_map);
                        let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: ConfigMap::api_resource(),
                            name: make_config_map_name(zk),
                            namespace: zk.metadata().namespace().unwrap(),
                            obj: new_config_map.to_dynamic_object(),
                        });
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterUpdateConfigMap,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req_o)));
                    }
                } else if get_cm_resp.unwrap_err().is_object_not_found() {
                    // Create the config map since it doesn't exist yet.
                    let config_map = make_config_map(zk);
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: ConfigMap::api_resource(),
                        namespace: zk.metadata().namespace().unwrap(),
                        obj: config_map.to_dynamic_object(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateConfigMap,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterCreateConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response() {
                let create_cm_resp = resp_o.unwrap().into_k_response().into_create_response().res;
                if create_cm_resp.is_ok() {
                    let create_cm_result = ConfigMap::from_dynamic_object(create_cm_resp.unwrap());
                    if create_cm_result.is_ok() {
                        let latest_config_map = create_cm_result.unwrap();
                        if latest_config_map.metadata().resource_version().is_some() {
                            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                                api_resource: StatefulSet::api_resource(),
                                name: make_stateful_set_name(zk),
                                namespace: zk.metadata().namespace().unwrap(),
                            });
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet,
                                latest_config_map_rv_opt: latest_config_map.metadata().resource_version(),
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req_o)));
                        }
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterUpdateConfigMap => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response() {
                let update_cm_resp = resp_o.unwrap().into_k_response().into_update_response().res;
                if update_cm_resp.is_ok() {
                    let update_cm_result = ConfigMap::from_dynamic_object(update_cm_resp.unwrap());
                    if update_cm_result.is_ok() {
                        let latest_config_map = update_cm_result.unwrap();
                        if latest_config_map.metadata().resource_version().is_some() {
                            let req_o = KubeAPIRequest::GetRequest(KubeGetRequest {
                                api_resource: StatefulSet::api_resource(),
                                name: make_stateful_set_name(zk),
                                namespace: zk.metadata().namespace().unwrap(),
                            });
                            let state_prime = ZookeeperReconcileState {
                                reconcile_step: ZookeeperReconcileStep::AfterGetStatefulSet,
                                latest_config_map_rv_opt: latest_config_map.metadata().resource_version(),
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req_o)));
                        }
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterGetStatefulSet => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_get_response() {
                let get_sts_resp = resp_o.unwrap().into_k_response().into_get_response().res;
                if get_sts_resp.is_ok() {
                    let get_sts_result = StatefulSet::from_dynamic_object(get_sts_resp.unwrap());
                    if get_sts_result.is_ok() {
                        let found_stateful_set = get_sts_result.unwrap();
                        // Updating the stateful set can lead to downscale,
                        // which also requires to remove the zookeeper replica from the membership list explicitly.
                        // If the zookeeper replica is deleted without being removed from the membership,
                        // the zookeeper cluster might be unavailable because of losing the quorum.
                        // So the controller needs to correctly prompt membership change before reducing the replica
                        // size of the stateful set, by writing the new replica size into the zookeeper API.
                        // Details can be found in https://github.com/vmware-research/verifiable-controllers/issues/174.
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterExistsZKNode,
                            // Save the stateful set found by the get request.
                            // Later when we want to update sts, we can use the old sts as the base
                            // and we do not need to call GetRequest again.
                            found_stateful_set_opt: Some(found_stateful_set),
                            ..state
                        };
                        let node_path = zk_node_path(zk);
                        let ext_req = ZKAPIInput::ExistsRequest(
                            zk.metadata().name().unwrap(), zk.metadata().namespace().unwrap(), zk.spec().client_port(), node_path
                        );
                        return (state_prime, Some(Request::ExternalRequest(ext_req)));
                    }
                } else if get_sts_resp.unwrap_err().is_object_not_found() && state.latest_config_map_rv_opt.is_some() {
                    // Create the stateful set since it doesn't exist yet.
                    let stateful_set = make_stateful_set(zk, state.latest_config_map_rv_opt.as_ref().unwrap());
                    let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: StatefulSet::api_resource(),
                        namespace: zk.metadata().namespace().unwrap(),
                        obj: stateful_set.to_dynamic_object(),
                    });
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateStatefulSet,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req_o)));
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterExistsZKNode => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_external_response()
            && resp_o.as_ref().unwrap().as_external_response_ref().is_exists_response() {
                let exists_resp = resp_o.unwrap().into_external_response().unwrap_exists_response().res;
                if exists_resp.is_ok() {
                    let version_o = exists_resp.unwrap();
                    if version_o.is_some() {
                        let version = version_o.unwrap();
                        let node_path = zk_node_path(zk);
                        let data = zk_node_data(zk);
                        let ext_req = ZKAPIInput::SetDataRequest(
                            zk.metadata().name().unwrap(), zk.metadata().namespace().unwrap(), zk.spec().client_port(), node_path, data, version
                        );
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterUpdateZKNode,
                            ..state
                        };
                        return (state_prime, Some(Request::ExternalRequest(ext_req)));
                    } else {
                        let node_path = zk_parent_node_path(zk);
                        let data = new_strlit("").to_string();
                        let ext_req = ZKAPIInput::CreateRequest(
                            zk.metadata().name().unwrap(), zk.metadata().namespace().unwrap(), zk.spec().client_port(), node_path, data
                        );
                        let state_prime = ZookeeperReconcileState {
                            reconcile_step: ZookeeperReconcileStep::AfterCreateZKParentNode,
                            ..state
                        };
                        return (state_prime, Some(Request::ExternalRequest(ext_req)));
                    }
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterCreateZKParentNode => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_external_response()
            && resp_o.as_ref().unwrap().as_external_response_ref().is_create_response() {
                let create_resp = resp_o.unwrap().into_external_response().unwrap_create_response().res;
                if create_resp.is_ok() || create_resp.unwrap_err().is_create_already_exists() {
                    let node_path = zk_node_path(zk);
                    let data = zk_node_data(zk);
                    let ext_req = ZKAPIInput::CreateRequest(
                        zk.metadata().name().unwrap(), zk.metadata().namespace().unwrap(), zk.spec().client_port(), node_path, data
                    );
                    let state_prime = ZookeeperReconcileState {
                        reconcile_step: ZookeeperReconcileStep::AfterCreateZKNode,
                        ..state
                    };
                    return (state_prime, Some(Request::ExternalRequest(ext_req)));
                }
            }
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Error,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterCreateZKNode => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_external_response()
            && resp_o.as_ref().unwrap().as_external_response_ref().is_create_response()
            && resp_o.unwrap().into_external_response().unwrap_create_response().res.is_ok()
            && state.found_stateful_set_opt.is_some() && state.latest_config_map_rv_opt.is_some() {
                // Update the stateful set only after we ensure
                // that the ZK node has been set correctly.
                let found_stateful_set = state.found_stateful_set_opt.as_ref().unwrap();
                let latest_config_map_rv = state.latest_config_map_rv_opt.as_ref().unwrap();
                let new_stateful_set = update_stateful_set(zk, found_stateful_set, latest_config_map_rv);
                let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                    api_resource: StatefulSet::api_resource(),
                    name: make_stateful_set_name(zk),
                    namespace: zk.metadata().namespace().unwrap(),
                    obj: new_stateful_set.to_dynamic_object(),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterUpdateStatefulSet,
                    found_stateful_set_opt: None,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                return (state_prime, None);
            }
        },
        ZookeeperReconcileStep::AfterUpdateZKNode => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_external_response()
            && resp_o.as_ref().unwrap().as_external_response_ref().is_set_data_response()
            && resp_o.unwrap().into_external_response().unwrap_set_data_response().res.is_ok()
            && state.found_stateful_set_opt.is_some() && state.latest_config_map_rv_opt.is_some() {
                // Update the stateful set only after we ensure
                // that the ZK node has been set correctly.
                let found_stateful_set = state.found_stateful_set_opt.as_ref().unwrap();
                let latest_config_map_rv = state.latest_config_map_rv_opt.as_ref().unwrap();
                let new_stateful_set = update_stateful_set(zk, found_stateful_set, latest_config_map_rv);
                let req_o = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                    api_resource: StatefulSet::api_resource(),
                    name: make_stateful_set_name(zk),
                    namespace: zk.metadata().namespace().unwrap(),
                    obj: new_stateful_set.to_dynamic_object(),
                });
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::AfterUpdateStatefulSet,
                    found_stateful_set_opt: None,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req_o)));
            } else {
                let state_prime = ZookeeperReconcileState {
                    reconcile_step: ZookeeperReconcileStep::Error,
                    ..state
                };
                return (state_prime, None);
            }
        },
        ZookeeperReconcileStep::AfterCreateStatefulSet => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Done,
                ..state
            };
            return (state_prime, None);
        },
        ZookeeperReconcileStep::AfterUpdateStatefulSet => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: ZookeeperReconcileStep::Done,
                ..state
            };
            return (state_prime, None);
        },
        _ => {
            let state_prime = ZookeeperReconcileState {
                reconcile_step: step,
                ..state
            };
            return (state_prime, None);
        }
    }
}

fn zk_node_path(zk: &ZookeeperCluster) -> (path: Vec<String>)
    requires
        zk@.well_formed(),
    ensures
        path@.map_values(|s: String| s@) == zk_spec::zk_node_path(zk@),
{
    let mut path = Vec::new();
    path.push(new_strlit("zookeeper-operator").to_string());
    path.push(zk.metadata().name().unwrap());
    proof {
        assert_seqs_equal!(path@.map_values(|s: String| s@), zk_spec::zk_node_path(zk@));
    }
    path
}

fn zk_parent_node_path(zk: &ZookeeperCluster) -> (path: Vec<String>)
    requires
        zk@.well_formed(),
    ensures
        path@.map_values(|s: String| s@) == zk_spec::zk_parent_node_path(zk@),
{
    let mut path = Vec::new();
    path.push(new_strlit("zookeeper-operator").to_string());
    proof {
        assert_seqs_equal!(path@.map_values(|s: String| s@), zk_spec::zk_parent_node_path(zk@));
    }
    path
}

fn zk_node_data(zk: &ZookeeperCluster) -> (data: String)
    requires
        zk@.well_formed(),
    ensures
        data@ == zk_spec::zk_node_data(zk@),
{
    new_strlit("CLUSTER_SIZE=").to_string().concat(i32_to_string(zk.spec().replicas()).as_str())
}

/// Headless Service is used to assign DNS entry to each zookeeper server Pod
fn make_headless_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.well_formed(),
    ensures
        service@ == zk_spec::make_headless_service(zk@),
{
    let mut ports = Vec::new();

    ports.push(ServicePort::new_with(new_strlit("tcp-client").to_string(), zk.spec().client_port()));
    ports.push(ServicePort::new_with(new_strlit("tcp-quorum").to_string(), 2888));
    ports.push(ServicePort::new_with(new_strlit("tcp-leader-election").to_string(), 3888));
    ports.push(ServicePort::new_with(new_strlit("tcp-metrics").to_string(), 7000));
    ports.push(ServicePort::new_with(new_strlit("tcp-admin-server").to_string(), 8080));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_headless_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, zk.metadata().name().unwrap().concat(new_strlit("-headless")), ports, false)
}

/// Client Service is used for any client to connect to the zookeeper server
fn make_client_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.well_formed(),
    ensures
        service@ == zk_spec::make_client_service(zk@),
{
    let mut ports = Vec::new();

    ports.push(ServicePort::new_with(new_strlit("tcp-client").to_string(), zk.spec().client_port()));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_client_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, zk.metadata().name().unwrap().concat(new_strlit("-client")), ports, true)
}

/// Admin-server Service is used for client to connect to admin server
fn make_admin_server_service(zk: &ZookeeperCluster) -> (service: Service)
    requires
        zk@.well_formed(),
    ensures
        service@ == zk_spec::make_admin_server_service(zk@),
{
    let mut ports = Vec::new();

    ports.push(ServicePort::new_with(new_strlit("tcp-admin-server").to_string(), 8080));

    proof {
        assert_seqs_equal!(
            ports@.map_values(|port: ServicePort| port@),
            zk_spec::make_admin_server_service(zk@).spec.get_Some_0().ports.get_Some_0()
        );
    }

    make_service(zk, zk.metadata().name().unwrap().concat(new_strlit("-admin-server")), ports, true)
}

/// make_service constructs the Service object given the name, ports and cluster_ip
fn make_service(zk: &ZookeeperCluster, name: String, ports: Vec<ServicePort>, cluster_ip: bool) -> (service: Service)
    requires
        zk@.well_formed(),
    ensures
        service@ == zk_spec::make_service(zk@, name@, ports@.map_values(|port: ServicePort| port@), cluster_ip),
{
    let mut service = Service::default();
    service.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(name);
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), zk.metadata().name().unwrap());
            labels
        });
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(zk.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    zk_spec::make_service(zk@, name@, ports@.map_values(|port: ServicePort| port@), cluster_ip).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
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
            selector.insert(new_strlit("app").to_string(), zk.metadata().name().unwrap());
            selector
        });
        service_spec
    });

    service
}

fn make_config_map_name(zk: &ZookeeperCluster) -> (name: String)
    requires
        zk@.well_formed(),
    ensures
        name@ == zk_spec::make_config_map_name(zk@.metadata.name.get_Some_0()),
{
    zk.metadata().name().unwrap().concat(new_strlit("-configmap"))
}

fn update_config_map(zk: &ZookeeperCluster, found_config_map: &ConfigMap) -> (config_map: ConfigMap)
    requires
        zk@.well_formed(),
    ensures
        config_map@ == zk_spec::update_config_map(zk@, found_config_map@),
{
    let mut config_map = found_config_map.clone();
    let made_config_map = make_config_map(zk);
    config_map.set_metadata({
        let mut metadata = found_config_map.metadata();
        metadata.set_labels(made_config_map.metadata().labels().unwrap());
        metadata
    });
    config_map.set_data(made_config_map.data().unwrap());
    config_map
}

/// The ConfigMap stores the configuration data of zookeeper servers
fn make_config_map(zk: &ZookeeperCluster) -> (config_map: ConfigMap)
    requires
        zk@.well_formed(),
    ensures
        config_map@ == zk_spec::make_config_map(zk@),
{
    let mut config_map = ConfigMap::default();

    config_map.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_config_map_name(zk));
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), zk.metadata().name().unwrap());
            labels
        });
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(zk.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    zk_spec::make_config_map(zk@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
        metadata
    });
    config_map.set_data({
        let mut data = StringMap::empty();
        data.insert(new_strlit("zoo.cfg").to_string(), make_zk_config(zk));
        data.insert(new_strlit("log4j.properties").to_string(), make_log4j_config());
        data.insert(new_strlit("log4j-quiet.properties").to_string(), make_log4j_quiet_config());
        data.insert(new_strlit("env.sh").to_string(), make_env_config(zk));
        data
    });

    config_map
}

fn make_zk_config(zk: &ZookeeperCluster) -> (s: String)
    ensures
        s@ == zk_spec::make_zk_config(zk@),
{
    new_strlit(
        "4lw.commands.whitelist=cons, envi, conf, crst, srvr, stat, mntr, ruok\n\
        dataDir=/data\n\
        standaloneEnabled=false\n\
        reconfigEnabled=true\n\
        skipACL=yes\n\
        metricsProvider.className=org.apache.zookeeper.metrics.prometheus.PrometheusMetricsProvider\n\
        metricsProvider.httpPort=7000\n\
        metricsProvider.exportJvmInfo=true\n\
        initLimit=").to_string().concat(i32_to_string(zk.spec().conf().init_limit()).as_str()).concat(new_strlit("\n\
        syncLimit=")).concat(i32_to_string(zk.spec().conf().sync_limit()).as_str()).concat(new_strlit("\n\
        tickTime=")).concat(i32_to_string(zk.spec().conf().tick_time()).as_str()).concat(new_strlit("\n\
        globalOutstandingLimit=")).concat(i32_to_string(zk.spec().conf().global_outstanding_limit()).as_str()).concat(new_strlit("\n\
        preAllocSize=")).concat(i32_to_string(zk.spec().conf().pre_alloc_size()).as_str()).concat(new_strlit("\n\
        snapCount=")).concat(i32_to_string(zk.spec().conf().snap_count()).as_str()).concat(new_strlit("\n\
        commitLogCount=")).concat(i32_to_string(zk.spec().conf().commit_log_count()).as_str()).concat(new_strlit("\n\
        snapSizeLimitInKb=")).concat(i32_to_string(zk.spec().conf().snap_size_limit_in_kb()).as_str()).concat(new_strlit("\n\
        maxCnxns=")).concat(i32_to_string(zk.spec().conf().max_cnxns()).as_str()).concat(new_strlit("\n\
        maxClientCnxns=")).concat(i32_to_string(zk.spec().conf().max_client_cnxns()).as_str()).concat(new_strlit("\n\
        minSessionTimeout=")).concat(i32_to_string(zk.spec().conf().min_session_timeout()).as_str()).concat(new_strlit("\n\
        maxSessionTimeout=")).concat(i32_to_string(zk.spec().conf().max_session_timeout()).as_str()).concat(new_strlit("\n\
        autopurge.snapRetainCount=")).concat(i32_to_string(zk.spec().conf().auto_purge_snap_retain_count()).as_str()).concat(new_strlit("\n\
        autopurge.purgeInterval=")).concat(i32_to_string(zk.spec().conf().auto_purge_purge_interval()).as_str()).concat(new_strlit("\n\
        quorumListenOnAllIPs=")).concat(bool_to_string(zk.spec().conf().quorum_listen_on_all_ips()).as_str()).concat(new_strlit("\n\
        admin.serverPort=8080\n\
        dynamicConfigFile=/data/zoo.cfg.dynamic\n"
    ))
}

fn make_log4j_config() -> (s: String)
    ensures
        s@ == zk_spec::make_log4j_config(),
{
    new_strlit(
        "zookeeper.root.logger=CONSOLE\n\
        zookeeper.console.threshold=INFO\n\
        log4j.rootLogger=${zookeeper.root.logger}\n\
        log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n\
        log4j.appender.CONSOLE.Threshold=${zookeeper.console.threshold}\n\
        log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n\
        log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    ).to_string()
}

fn make_log4j_quiet_config() -> (s: String)
    ensures
        s@ == zk_spec::make_log4j_quiet_config(),
{
    new_strlit(
        "log4j.rootLogger=ERROR, CONSOLE\n\
        log4j.appender.CONSOLE=org.apache.log4j.ConsoleAppender\n\
        log4j.appender.CONSOLE.Threshold=ERROR\n\
        log4j.appender.CONSOLE.layout=org.apache.log4j.PatternLayout\n\
        log4j.appender.CONSOLE.layout.ConversionPattern=%d{ISO8601} [myid:%X{myid}] - %-5p [%t:%C{1}@%L] - %m%n\n"
    ).to_string()
}

fn make_env_config(zk: &ZookeeperCluster) -> (s: String)
    requires
        zk@.well_formed(),
    ensures
        s@ == zk_spec::make_env_config(zk@),
{
    let name = zk.metadata().name().unwrap();
    let namespace = zk.metadata().namespace().unwrap();
    let client_port = i32_to_string(zk.spec().client_port());

    new_strlit(
        "#!/usr/bin/env bash\n\n\
        DOMAIN=").to_string().concat(name.as_str()).concat(new_strlit("-headless.")).concat(namespace.as_str())
            .concat(new_strlit(".svc.cluster.local\n\
        QUORUM_PORT=2888\n\
        LEADER_PORT=3888\n\
        CLIENT_HOST=")).concat(name.as_str()).concat(new_strlit("-client\n\
        CLIENT_PORT=")).concat(client_port.as_str()).concat(new_strlit("\n\
        ADMIN_SERVER_HOST=")).concat(name.as_str()).concat(new_strlit("-admin-server\n\
        ADMIN_SERVER_PORT=8080\n\
        CLUSTER_NAME=")).concat(name.as_str()).concat(new_strlit("\n\
        CLUSTER_SIZE=")).concat(i32_to_string(zk.spec().replicas()).as_str()).concat(new_strlit("\n"))
}

fn make_stateful_set_name(zk: &ZookeeperCluster) -> (name: String)
    requires
        zk@.well_formed(),
    ensures
        name@ == zk_spec::make_stateful_set_name(zk@.metadata.name.get_Some_0()),
{
    zk.metadata().name().unwrap()
}

fn update_stateful_set(zk: &ZookeeperCluster, found_stateful_set: &StatefulSet, rv: &String) -> (stateful_set: StatefulSet)
    requires
        zk@.well_formed(),
    ensures
        stateful_set@ == zk_spec::update_stateful_set(zk@, found_stateful_set@, rv@),
{
    let mut stateful_set = found_stateful_set.clone();
    let made_stateful_set = make_stateful_set(zk, rv);
    stateful_set.set_metadata({
        let mut metadata = found_stateful_set.metadata();
        metadata.set_labels(made_stateful_set.metadata().labels().unwrap());
        metadata
    });
    stateful_set.set_spec(made_stateful_set.spec().unwrap());
    stateful_set
}

/// The StatefulSet manages the zookeeper server containers (as Pods)
/// and the volumes attached to each server (as PersistentVolumeClaims)
fn make_stateful_set(zk: &ZookeeperCluster, rv: &String) -> (stateful_set: StatefulSet)
    requires
        zk@.well_formed(),
    ensures
        stateful_set@ == zk_spec::make_stateful_set(zk@, rv@),
{
    let mut stateful_set = StatefulSet::default();
    stateful_set.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_stateful_set_name(zk));
        metadata.set_labels({
            let mut labels = StringMap::empty();
            labels.insert(new_strlit("app").to_string(), zk.metadata().name().unwrap());
            labels
        });
        metadata.set_owner_references({
            let mut owner_references = Vec::new();
            owner_references.push(zk.controller_owner_ref());
            proof {
                assert_seqs_equal!(
                    owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                    zk_spec::make_stateful_set(zk@, rv@).metadata.owner_references.get_Some_0()
                );
            }
            owner_references
        });
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
            selector.set_match_labels({
                let mut match_labels = StringMap::empty();
                match_labels.insert(new_strlit("app").to_string(), zk.metadata().name().unwrap());
                match_labels
            });
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
                metadata.set_generate_name(zk.metadata().name().unwrap());
                metadata.set_labels({
                    let mut labels = StringMap::empty();
                    labels.insert(new_strlit("app").to_string(), zk.metadata().name().unwrap());
                    labels.insert(new_strlit("kind").to_string(), new_strlit("ZookeeperMember").to_string());
                    labels
                });
                metadata.set_annotations({
                    let mut annotations = StringMap::empty();
                    annotations.insert(new_strlit("config").to_string(), rv.clone());
                    annotations
                });
                metadata
            });
            pod_template_spec.set_spec(make_zk_pod_spec(zk));
            pod_template_spec
        });
        // Set the templates used for creating the persistent volume claims attached to each pod
        stateful_set_spec.set_volume_claim_templates({
            let mut volume_claim_templates = Vec::new();
            volume_claim_templates.push({
                let mut pvc = PersistentVolumeClaim::default();
                pvc.set_metadata({
                    let mut metadata = ObjectMeta::default();
                    metadata.set_name(new_strlit("data").to_string());
                    metadata.set_labels({
                        let mut labels = StringMap::empty();
                        labels.insert(new_strlit("app").to_string(), zk.metadata().name().unwrap());
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
                                zk_spec::make_stateful_set(zk@, rv@)
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
                            requests.insert(new_strlit("storage").to_string(), new_strlit("20Gi").to_string());
                            requests
                        });
                        resources
                    });
                    pvc_spec
                });
                pvc
            });

            proof {
                assert_seqs_equal!(
                    volume_claim_templates@.map_values(|pvc: PersistentVolumeClaim| pvc@),
                    zk_spec::make_stateful_set(zk@, rv@).spec.get_Some_0().volume_claim_templates.get_Some_0()
                );
            }

            volume_claim_templates
        });
        stateful_set_spec
    });
    stateful_set
}

fn make_zk_pod_spec(zk: &ZookeeperCluster) -> (pod_spec: PodSpec)
    requires
        zk@.well_formed(),
    ensures
        pod_spec@ == zk_spec::make_zk_pod_spec(zk@),
{
    let mut pod_spec = PodSpec::default();

    pod_spec.set_containers({
        let mut containers = Vec::new();
        containers.push({
            let mut zk_container = Container::default();
            zk_container.set_name(new_strlit("zookeeper").to_string());
            zk_container.set_image(zk.spec().image());
            zk_container.set_command({
                let mut command = Vec::new();
                command.push(new_strlit("/usr/local/bin/zookeeperStart.sh").to_string());
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
                                    zk_spec::make_zk_pod_spec(zk@).containers[0].lifecycle.get_Some_0().pre_stop.get_Some_0().exec_.get_Some_0().command.get_Some_0()
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
            zk_container.set_resources(zk.spec().resources());
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
                        zk_spec::make_zk_pod_spec(zk@).containers[0].volume_mounts.get_Some_0()
                    );
                }

                volume_mounts
            });
            zk_container.set_ports({
                let mut ports = Vec::new();
                ports.push(ContainerPort::new_with(new_strlit("client").to_string(), zk.spec().client_port()));
                ports.push(ContainerPort::new_with(new_strlit("quorum").to_string(), 2888));
                ports.push(ContainerPort::new_with(new_strlit("leader-election").to_string(), 3888));
                ports.push(ContainerPort::new_with(new_strlit("metrics").to_string(), 7000));
                ports.push(ContainerPort::new_with(new_strlit("admin-server").to_string(), 8080));

                proof {
                    assert_seqs_equal!(
                        ports@.map_values(|port: ContainerPort| port@),
                        zk_spec::make_zk_pod_spec(zk@).containers[0].ports.get_Some_0()
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
                                zk_spec::make_zk_pod_spec(zk@).containers[0].readiness_probe.get_Some_0().exec_.get_Some_0().command.get_Some_0()
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
                                zk_spec::make_zk_pod_spec(zk@).containers[0].liveness_probe.get_Some_0().exec_.get_Some_0().command.get_Some_0()
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
                zk_spec::make_zk_pod_spec(zk@).containers
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

        proof {
            assert_seqs_equal!(
                volumes@.map_values(|vol: Volume| vol@),
                zk_spec::make_zk_pod_spec(zk@).volumes.get_Some_0()
            );
        }

        volumes
    });

    pod_spec
}

}
