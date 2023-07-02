// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    controller::controller_runtime::{continue_reconcile, end_reconcile, run_scheduled_reconcile},
    message::*,
};
use crate::temporal_logic::defs::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::{reconciler::*, zookeepercluster::*};
use vstd::prelude::*;

verus! {

pub type ClusterState = State<ZookeeperClusterView, ZookeeperReconcileState>;

pub open spec fn cluster_spec() -> TempPred<ClusterState> {
    sm_spec::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()
}

// Handy abbreviation for Init step
pub open spec fn at_init_step(key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.reconcile_state_contains(key)
        &&& s.reconcile_state_of(key).local_state.reconcile_step.is_Init()
    }
}

pub open spec fn at_init_step_with_zk(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.reconcile_state_contains(zk.object_ref())
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
        &&& s.reconcile_state_of(zk.object_ref()).local_state.reconcile_step.is_Init()
    }
}

pub open spec fn at_init_step_with_no_pending_req(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_init_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_None()
    }
}

// Handy abbreviation for AfterCreateHeadlessService step
pub open spec fn at_after_create_headless_service_step(key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.reconcile_state_contains(key)
        &&& s.reconcile_state_of(key).local_state.reconcile_step.is_AfterCreateHeadlessService()
    }
}

pub open spec fn at_after_create_headless_service_step_with_zk(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.reconcile_state_contains(zk.object_ref())
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
        &&& s.reconcile_state_of(zk.object_ref()).local_state.reconcile_step.is_AfterCreateHeadlessService()
    }
}

pub open spec fn is_create_headless_service_request_msg(msg: Message, zk: ZookeeperClusterView) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_create_request()
    &&& msg.content.get_create_request().namespace == zk.metadata.namespace.get_Some_0()
    &&& msg.content.get_create_request().obj == make_headless_service(zk).to_dynamic_object()
}

pub open spec fn at_after_create_headless_service_step_with_zk_and_pending_req_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_headless_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& s.message_in_flight(s.pending_req_of(zk.object_ref()))
        &&& is_create_headless_service_request_msg(s.pending_req_of(zk.object_ref()), zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_headless_service_step_with_zk(
    zk: ZookeeperClusterView, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_headless_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg == Option::Some(req_msg)
        &&& s.message_in_flight(req_msg)
        &&& is_create_headless_service_request_msg(req_msg, zk)
    }
}

pub open spec fn at_after_create_headless_service_step_with_zk_and_exists_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_headless_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_create_headless_service_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_after_create_headless_service_step_with_zk(
    zk: ZookeeperClusterView, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_headless_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_create_headless_service_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
    }
}

pub open spec fn at_zookeeper_step(key: ObjectRef, step: ZookeeperReconcileStep) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: ClusterState| {
        &&& s.reconcile_state_contains(key)
        &&& s.reconcile_state_of(key).local_state.reconcile_step == step
    }
}

pub open spec fn at_after_create_client_service_step_with_zk(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.reconcile_state_contains(zk.object_ref())
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
        &&& s.reconcile_state_of(zk.object_ref()).local_state.reconcile_step.is_AfterCreateClientService()
    }
}

pub open spec fn is_create_client_service_request_msg(msg: Message, zk: ZookeeperClusterView) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_create_request()
    &&& msg.content.get_create_request().namespace == zk.metadata.namespace.get_Some_0()
    &&& msg.content.get_create_request().obj == make_client_service(zk).to_dynamic_object()
}

pub open spec fn at_after_create_client_service_step_with_zk_and_pending_req_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_client_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& s.message_in_flight(s.pending_req_of(zk.object_ref()))
        &&& is_create_client_service_request_msg(s.pending_req_of(zk.object_ref()), zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_client_service_step_with_zk(
    zk: ZookeeperClusterView, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_client_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg == Option::Some(req_msg)
        &&& s.message_in_flight(req_msg)
        &&& is_create_client_service_request_msg(req_msg, zk)
    }
}

pub open spec fn at_after_create_client_service_step_with_zk_and_exists_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_client_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_create_client_service_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_after_create_client_service_step_with_zk(
    zk: ZookeeperClusterView, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_client_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_create_client_service_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
    }
}

pub open spec fn at_after_create_admin_server_service_step_with_zk(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.reconcile_state_contains(zk.object_ref())
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
        &&& s.reconcile_state_of(zk.object_ref()).local_state.reconcile_step.is_AfterCreateAdminServerService()
    }
}

pub open spec fn is_create_admin_server_service_request_msg(msg: Message, zk: ZookeeperClusterView) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_create_request()
    &&& msg.content.get_create_request().namespace == zk.metadata.namespace.get_Some_0()
    &&& msg.content.get_create_request().obj == make_admin_server_service(zk).to_dynamic_object()
}

pub open spec fn at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_admin_server_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& s.message_in_flight(s.pending_req_of(zk.object_ref()))
        &&& is_create_admin_server_service_request_msg(s.pending_req_of(zk.object_ref()), zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_admin_server_service_step_with_zk(
    zk: ZookeeperClusterView, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_admin_server_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg == Option::Some(req_msg)
        &&& s.message_in_flight(req_msg)
        &&& is_create_admin_server_service_request_msg(req_msg, zk)
    }
}

pub open spec fn at_after_create_admin_server_service_step_with_zk_and_exists_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_admin_server_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_create_admin_server_service_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_after_create_admin_server_service_step_with_zk(
    zk: ZookeeperClusterView, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_admin_server_service_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_create_admin_server_service_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
    }
}

pub open spec fn at_after_create_config_map_step_with_zk(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.reconcile_state_contains(zk.object_ref())
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
        &&& s.reconcile_state_of(zk.object_ref()).local_state.reconcile_step.is_AfterCreateConfigMap()
    }
}

pub open spec fn is_create_config_map_request_msg(msg: Message, zk: ZookeeperClusterView) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_create_request()
    &&& msg.content.get_create_request().namespace == zk.metadata.namespace.get_Some_0()
    &&& msg.content.get_create_request().obj == make_config_map(zk).to_dynamic_object()
}

pub open spec fn at_after_create_config_map_step_with_zk_and_pending_req_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_config_map_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& s.message_in_flight(s.pending_req_of(zk.object_ref()))
        &&& is_create_config_map_request_msg(s.pending_req_of(zk.object_ref()), zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_config_map_step_with_zk(
    zk: ZookeeperClusterView, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_config_map_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg == Option::Some(req_msg)
        &&& s.message_in_flight(req_msg)
        &&& is_create_config_map_request_msg(req_msg, zk)
    }
}

pub open spec fn at_after_create_config_map_step_with_zk_and_exists_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_config_map_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_create_config_map_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_after_create_config_map_step_with_zk(
    zk: ZookeeperClusterView, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_config_map_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_create_config_map_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)(s)
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
    }
}

pub open spec fn is_get_stateful_set_request_msg(msg: Message, zk: ZookeeperClusterView) -> bool
    recommends
        zk.well_formed(),
{
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_get_request()
    &&& msg.content.get_get_request().key == ObjectRef {
        kind: StatefulSetView::kind(),
        name: make_stateful_set_name(zk.metadata.name.get_Some_0()),
        namespace: zk.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_get_stateful_set_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& s.message_in_flight(s.pending_req_of(zk.object_ref()))
        &&& is_get_stateful_set_request_msg(s.pending_req_of(zk.object_ref()), zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step_with_zk(
    zk: ZookeeperClusterView, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_get_stateful_set_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg == Option::Some(req_msg)
        &&& s.message_in_flight(req_msg)
        &&& is_get_stateful_set_request_msg(req_msg, zk)
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk_and_exists_ok_resp_in_flight(
    zk: ZookeeperClusterView, object: DynamicObjectView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_get_stateful_set_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_get_stateful_set_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
        }
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk_and_exists_not_found_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_get_stateful_set_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_get_stateful_set_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk_and_exists_not_found_err_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_get_stateful_set_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_get_stateful_set_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_after_get_stateful_set_step_with_zk(
    zk: ZookeeperClusterView, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_get_stateful_set_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_get_stateful_set_request_msg(s.pending_req_of(zk.object_ref()), zk)
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
    }
}

pub open spec fn at_after_create_stateful_set_step_with_zk(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)(s)
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
    }
}

pub open spec fn is_create_stateful_set_request_msg(
    msg: Message, zk: ZookeeperClusterView
) -> bool
    recommends
        zk.well_formed(),
{
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_create_request()
    &&& msg.content.get_create_request().namespace == zk.metadata.namespace.get_Some_0()
    &&& msg.content.get_create_request().obj == make_stateful_set(zk).to_dynamic_object()
}

pub open spec fn at_after_create_stateful_set_step_with_zk_and_pending_req_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_stateful_set_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& s.message_in_flight(s.pending_req_of(zk.object_ref()))
        &&& is_create_stateful_set_request_msg(s.pending_req_of(zk.object_ref()), zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_stateful_set_step_with_zk(
    zk: ZookeeperClusterView, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_create_stateful_set_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg == Option::Some(req_msg)
        &&& s.message_in_flight(req_msg)
        &&& is_create_stateful_set_request_msg(req_msg, zk)
    }
}

// Handy abbreviation for AfterUpdateStatefulSet step

pub open spec fn at_after_update_stateful_set_step(key: ObjectRef) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        &&& s.reconcile_state_contains(key)
        &&& s.reconcile_state_of(key).local_state.reconcile_step.is_AfterUpdateStatefulSet()
    }
}

pub open spec fn at_after_update_stateful_set_step_with_zk(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)(s)
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
    }
}

pub open spec fn is_update_stateful_set_request_msg(
    msg: Message, zk: ZookeeperClusterView, object: DynamicObjectView
) -> bool
    recommends
        zk.well_formed(),
{
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_update_request()
    &&& msg.content.get_update_request().key == make_stateful_set_key(zk.object_ref())
    &&& msg.content.get_update_request().obj == update_stateful_set(
        zk, StatefulSetView::from_dynamic_object(object).get_Ok_0()
    ).to_dynamic_object()
}

pub open spec fn at_after_update_stateful_set_step_with_zk_and_pending_req_in_flight(
    zk: ZookeeperClusterView, object: DynamicObjectView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_update_stateful_set_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& s.message_in_flight(s.pending_req_of(zk.object_ref()))
        &&& is_update_stateful_set_request_msg(s.pending_req_of(zk.object_ref()), zk, object)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_update_stateful_set_step_with_zk(
    zk: ZookeeperClusterView, req_msg: Message, object: DynamicObjectView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_after_update_stateful_set_step_with_zk(zk)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg == Option::Some(req_msg)
        &&& s.message_in_flight(req_msg)
        &&& is_update_stateful_set_request_msg(req_msg, zk, object)
    }
}

// Handy abbreviation for Done step

pub open spec fn at_done_step(key: ObjectRef) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        &&& s.reconcile_state_contains(key)
        &&& s.reconcile_state_of(key).local_state.reconcile_step.is_Done()
    }
}

pub open spec fn at_done_step_with_zk(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_done_step(zk.object_ref())(s)
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
    }
}

}
