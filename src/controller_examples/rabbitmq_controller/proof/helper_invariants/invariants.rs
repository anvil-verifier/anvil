// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, error::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::common::*,
    spec::{reconciler::*, types::*},
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub open spec fn create_server_cm_req_msg_in_flight_implies_at_after_create_server_cm_step(key: ObjectRef) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& server_config_map_create_request_msg(key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s)
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& msg == s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()
        }
    }
}

pub open spec fn update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(key: ObjectRef) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& server_config_map_update_request_msg(key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s)
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& msg == s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()
        }
    }
}

pub proof fn lemma_true_leads_to_always_update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(spec: TempPred<RMQCluster>, key: ObjectRef)
    requires
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(key))))
        ),
{
    let requirements = |msg: RMQMessage, s: RMQCluster| {
        server_config_map_update_request_msg(key)(msg)
        ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s)
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& msg == s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()
        }
    };
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        let pending_msg = s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0();
        assert forall |msg| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg) implies requirements(msg, s_prime) by {
            if server_config_map_update_request_msg(key)(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_server_config_map_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }

        }
    }

    invariant_n!(
        spec, lift_action(stronger_next), lift_action(RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id())
    );
    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(key)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}


pub open spec fn every_update_server_cm_req_does_the_same(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        forall |msg: RMQMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& server_config_map_update_request_msg(rabbitmq.object_ref())(msg)
        } ==> msg.content.get_update_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ()))
            && msg.content.get_update_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    }
}

pub proof fn lemma_always_stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq)))),
{
    let inv = resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq);
    lemma_always_sts_create_request_msg_is_valid(spec, rabbitmq.object_ref());
    lemma_always_sts_update_request_msg_is_valid(spec, rabbitmq.object_ref());
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& sts_update_request_msg_is_valid(rabbitmq.object_ref())(s)
        &&& sts_create_request_msg_is_valid(rabbitmq.object_ref())(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(sts_update_request_msg_is_valid(rabbitmq.object_ref())),
        lift_state(sts_create_request_msg_is_valid(rabbitmq.object_ref()))
    );
    init_invariant(spec, RMQCluster::init(), stronger_next, inv);
}

pub proof fn lemma_true_leads_to_always_every_update_server_cm_req_does_the_same(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)))),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(every_update_server_cm_req_does_the_same(rabbitmq))))
        ),
{
    let requirements = |msg: RMQMessage, s: RMQCluster| {
        server_config_map_update_request_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_update_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ()))
        && msg.content.get_update_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    };
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: RMQMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        && msg.dst.is_KubernetesAPI() && msg.content.is_APIRequest() implies requirements(msg, s_prime) by {
            if !s.in_flight().contains(msg) && server_config_map_update_request_msg(rabbitmq.object_ref())(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                let key = rabbitmq.object_ref();
                lemma_server_config_map_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                let other_rmq = s.ongoing_reconciles()[key].triggering_cr;
                assert(other_rmq.object_ref() == rabbitmq.object_ref());
                assert(rabbitmq.spec() == other_rmq.spec());
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))
    );
    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(every_update_server_cm_req_does_the_same(rabbitmq)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_true_leads_to_always_no_delete_cm_req_is_in_flight(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq))))
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(no_delete_request_msg_in_flight_with_key(make_server_config_map_key(rabbitmq.object_ref())))))
        ),
{
    let key = rabbitmq.object_ref();
    let requirements = |msg: RMQMessage, s: RMQCluster| !{
        &&& msg.dst.is_KubernetesAPI()
        &&& msg.content.is_delete_request()
        &&& msg.content.get_delete_request().key == make_server_config_map_key(rabbitmq.object_ref())
    };

    let stronger_next = |s: RMQCluster, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::desired_state_is(rabbitmq)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq)(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
    };
    assert forall |s: RMQCluster, s_prime: RMQCluster| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: RMQMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.resources().contains_key(make_server_config_map_key(key)) {
                let owner_refs = s.resources()[make_server_config_map_key(key)].metadata.owner_references;
                assert(owner_refs == Some(seq![rabbitmq.controller_owner_ref()]));
                assert(owner_reference_to_object_reference(owner_refs.get_Some_0()[0], key.namespace) == key);
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq)),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed())
    );

    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_delete_request_msg_in_flight_with_key(make_server_config_map_key(rabbitmq.object_ref()))),
        lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub open spec fn every_update_sts_req_does_the_same(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        forall |msg: RMQMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& sts_update_request_msg(rabbitmq.object_ref())(msg)
        } ==> msg.content.get_update_request().obj.spec == StatefulSetView::marshal_spec(make_stateful_set(rabbitmq).spec)
            && msg.content.get_update_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    }
}

pub proof fn lemma_true_leads_to_always_every_update_sts_req_does_the_same(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)))),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(every_update_sts_req_does_the_same(rabbitmq))))
        ),
{
    let requirements = |msg: RMQMessage, s: RMQCluster| {
        sts_update_request_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_update_request().obj.spec == StatefulSetView::marshal_spec(make_stateful_set(rabbitmq).spec)
        && msg.content.get_update_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    };
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: RMQMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        && msg.dst.is_KubernetesAPI() && msg.content.is_APIRequest() implies requirements(msg, s_prime) by {
            if !s.in_flight().contains(msg) && sts_update_request_msg(rabbitmq.object_ref())(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                let key = rabbitmq.object_ref();
                lemma_stateful_set_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                let other_rmq = s.ongoing_reconciles()[key].triggering_cr;
                assert(rabbitmq.spec() == other_rmq.spec());
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))
    );
    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(every_update_sts_req_does_the_same(rabbitmq)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn every_create_sts_req_does_the_same(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        forall |msg: RMQMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& sts_create_request_msg(rabbitmq.object_ref())(msg)
        } ==> msg.content.get_create_request().obj.spec == StatefulSetView::marshal_spec(make_stateful_set(rabbitmq).spec)
            && msg.content.get_create_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    }
}

pub proof fn lemma_true_leads_to_always_every_create_sts_req_does_the_same(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)))),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(every_create_sts_req_does_the_same(rabbitmq))))
        ),
{
    let requirements = |msg: RMQMessage, s: RMQCluster| {
        sts_create_request_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_create_request().obj.spec == StatefulSetView::marshal_spec(make_stateful_set(rabbitmq).spec)
        && msg.content.get_create_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    };
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: RMQMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        && msg.dst.is_KubernetesAPI() && msg.content.is_APIRequest() implies requirements(msg, s_prime) by {
            if !s.in_flight().contains(msg) && sts_create_request_msg(rabbitmq.object_ref())(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                let key = rabbitmq.object_ref();
                lemma_stateful_set_create_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                let other_rmq = s.ongoing_reconciles()[key].triggering_cr;
                assert(rabbitmq.spec() == other_rmq.spec());
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))
    );
    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(every_create_sts_req_does_the_same(rabbitmq)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn every_create_server_cm_req_does_the_same(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        forall |msg: RMQMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& server_config_map_create_request_msg(rabbitmq.object_ref())(msg)
        } ==> msg.content.get_create_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ()))
            && msg.content.get_create_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    }
}

pub proof fn lemma_true_leads_to_always_every_create_server_cm_req_does_the_same(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)))),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(every_create_server_cm_req_does_the_same(rabbitmq))))
        ),
{
    let requirements = |msg: RMQMessage, s: RMQCluster| {
        server_config_map_create_request_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_create_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ()))
        && && msg.content.get_create_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    };
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: RMQMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        && msg.dst.is_KubernetesAPI() && msg.content.is_APIRequest() implies requirements(msg, s_prime) by {
            if !s.in_flight().contains(msg) && server_config_map_create_request_msg(rabbitmq.object_ref())(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                lemma_server_config_map_create_request_msg_implies_key_in_reconcile_equals(rabbitmq.object_ref(), s, s_prime, msg, step);
                let other_rmq = s.ongoing_reconciles()[rabbitmq.object_ref()].triggering_cr;
                assert(other_rmq == s.ongoing_reconciles()[other_rmq.object_ref()].triggering_cr);
                assert(rabbitmq.spec() == other_rmq.spec());
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))
    );
    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(every_create_server_cm_req_does_the_same(rabbitmq)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn create_sts_req_msg_in_flight_implies_at_after_create_sts_step(key: ObjectRef) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& sts_create_request_msg(key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateStatefulSet)(s)
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& msg == s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()
        }
    }
}

pub proof fn lemma_true_leads_to_always_create_sts_req_msg_in_flight_implies_at_after_create_sts_step(spec: TempPred<RMQCluster>, key: ObjectRef)
    requires
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(create_sts_req_msg_in_flight_implies_at_after_create_sts_step(key))))
        ),
{
    let requirements = |msg: RMQMessage, s: RMQCluster| {
        sts_create_request_msg(key)(msg)
        ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateStatefulSet)(s)
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& msg == s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()
        }
    };
    let stronger_next = |s: RMQCluster, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: RMQMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if sts_create_request_msg(key)(msg) {
                if !s.in_flight().contains(msg) {
                    let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                    lemma_stateful_set_create_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::crash_disabled()), lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id())
    );

    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(create_sts_req_msg_in_flight_implies_at_after_create_sts_step(key)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn update_sts_req_msg_in_flight_implies_at_after_update_sts_step(key: ObjectRef) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& sts_update_request_msg(key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s)
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& msg == s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()
        }
    }
}

pub proof fn lemma_true_leads_to_always_update_sts_req_msg_in_flight_implies_at_after_update_sts_step(spec: TempPred<RMQCluster>, key: ObjectRef)
    requires
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(update_sts_req_msg_in_flight_implies_at_after_update_sts_step(key))))
        ),
{
    let requirements = |msg: RMQMessage, s: RMQCluster| {
        sts_update_request_msg(key)(msg)
        ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s)
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& msg == s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()
        }
    };
    let stronger_next = |s: RMQCluster, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: RMQMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if sts_update_request_msg(key)(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_stateful_set_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::crash_disabled()), lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id())
    );

    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(update_sts_req_msg_in_flight_implies_at_after_update_sts_step(key)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn no_delete_request_msg_in_flight_with_key(key: ObjectRef) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |msg: RMQMessage| !{
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_KubernetesAPI()
            &&& msg.content.is_delete_request()
            &&& msg.content.get_delete_request().key == key
        }
    }
}

/// This lemma demonstrates how to use kubernetes_cluster::proof::kubernetes_api_liveness::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies
/// (referred to as lemma_X) to prove that the system will eventually enter a state where delete stateful set request messages
/// will never appear in flight.
///
/// As an example, we can look at how this lemma is proved.
/// - Precondition: The preconditions should include all precondtions used by lemma_X and other predicates which show that
///     the newly generated messages are as expected. ("expected" means not delete stateful set request messages in this lemma. Therefore,
///     we provide an invariant stateful_set_has_owner_reference_pointing_to_current_cr so that the grabage collector won't try
///     to send a delete request to delete the messsage.)
/// - Postcondition: spec |= true ~> [](forall |msg| as_expected(msg))
/// - Proof body: The proof consists of three parts.
///   + Come up with "requirements" for those newly created api request messages. Usually, just move the forall |msg| and
///     s.in_flight().contains(msg) in the statepred of final state (no_delete_sts_req_is_in_flight in this lemma, so we can
///     get the requirements in this lemma).
///   + Show that spec |= every_new_req_msg_if_in_flight_then_satisfies. Basically, use two assert forall to show that forall state and
///     its next state and forall messages, if the messages are newly generated, they must satisfy the "requirements" and always satisfies it
///     as long as it is in flight.
///   + Call lemma_X. If a correct "requirements" are provided, we can easily prove the equivalence of every_in_flight_req_msg_satisfies(requirements)
///     and the original statepred.
pub proof fn lemma_true_leads_to_always_no_delete_sts_req_is_in_flight(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq))))
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(no_delete_request_msg_in_flight_with_key(make_stateful_set_key(rabbitmq.object_ref())))))
        ),
{
    let key = rabbitmq.object_ref();
    let requirements = |msg: RMQMessage, s: RMQCluster| !{
        &&& msg.dst.is_KubernetesAPI()
        &&& msg.content.is_delete_request()
        &&& msg.content.get_delete_request().key == make_stateful_set_key(rabbitmq.object_ref())
    };

    let stronger_next = |s: RMQCluster, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::desired_state_is(rabbitmq)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq)(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
    };
    assert forall |s: RMQCluster, s_prime: RMQCluster| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: RMQMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.resources().contains_key(make_stateful_set_key(key)) {
                let owner_refs = s.resources()[make_stateful_set_key(key)].metadata.owner_references;
                assert(owner_refs == Some(seq![rabbitmq.controller_owner_ref()]));
                assert(owner_reference_to_object_reference(owner_refs.get_Some_0()[0], key.namespace) == key);
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq)),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed())
    );

    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_delete_request_msg_in_flight_with_key(make_stateful_set_key(rabbitmq.object_ref()))),
        lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

/// This spec tells that when the reconciler is at AfterGetStatefulSet, and there is a matched response, the reponse must be
/// sts_get_response_msg. This lemma is used to show that the response message, if is ok, has an object whose reference is
/// stateful_set_key. resp_msg_matches_req_msg doesn't talk about the object in response should match the key in request
/// so we need this extra spec and lemma.
///
/// If we don't have this, we have no idea of what is inside the response message.
pub open spec fn response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    let key = rabbitmq.object_ref();
    |s: RMQCluster| {
        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterGetStatefulSet)(s)
        ==> s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && sts_get_request_msg(key)(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            && (
                forall |msg: RMQMessage|
                    #[trigger] s.in_flight().contains(msg)
                    && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
                    ==> sts_get_response_msg(key)(msg)
            )
    }
}

pub proof fn lemma_always_response_at_after_get_stateful_set_step_is_sts_get_response(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq)))),
{
    let inv = response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq);
    let key = rabbitmq.object_ref();
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)(s_prime)
    };
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    RMQCluster::lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec, key);
    always_to_always_later(spec, lift_state(RMQCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        later(lift_state(RMQCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)))
    );
    init_invariant(spec, RMQCluster::init(), next, inv);
}

}
