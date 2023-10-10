// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::{common::*, helper_invariants::*, resource::*},
    spec::{reconciler::*, types::*, resource::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

spec fn replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        forall |msg: RMQMessage|
            #[trigger] s.in_flight().contains(msg)
            ==> (
                sts_create_request_msg(rabbitmq.object_ref())(msg)
                ==> replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s)
            ) && (
                sts_update_request_msg(rabbitmq.object_ref())(msg)
                ==> replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s)
            )
    }
}

proof fn replicas_of_stateful_set_update_request_msg_satisfies_order_induction(
    rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster, msg: RMQMessage
)
    requires
        RMQCluster::next()(s, s_prime),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s_prime),
        RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        RMQCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(rabbitmq)(s),
        object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references()(s),
        replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq)(s),
        s_prime.in_flight().contains(msg),
        sts_update_request_msg(rabbitmq.object_ref())(msg),
    ensures
        replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime),
{
    let step = choose |step| RMQCluster::next_step(s, s_prime, step);
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(key);
    match step {
        Step::KubernetesAPIStep(input) => {
            assert(s.in_flight().contains(msg));
            assert(s.controller_state == s_prime.controller_state);
            if s_prime.resources().contains_key(key) {
                if s.resources().contains_key(key) {
                    assert(replicas_of_rabbitmq(s.resources()[key]) <= replicas_of_rabbitmq(s_prime.resources()[key]));
                } else {
                    assert(s_prime.resources()[key].metadata.uid.is_Some());
                    assert(s_prime.resources()[key].metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                    let owner_refs = msg.content.get_update_request().obj.metadata.owner_references;
                    if owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1 {
                        assert(owner_refs.get_Some_0()[0].uid < s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                    }
                }
            }
            assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
        },
        Step::ControllerStep(input) => {
            if !s.in_flight().contains(msg) {
                StatefulSetView::marshal_spec_preserves_integrity();
                lemma_stateful_set_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                assert(StatefulSetView::unmarshal(msg.content.get_update_request().obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() <= s.ongoing_reconciles()[key].triggering_cr.spec.replicas);
            }
            assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
        },
        Step::ScheduleControllerReconcileStep(input) => {
            assert(s.in_flight().contains(msg));
            assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
            assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
        },
        Step::RestartController() => {
            assert(s.in_flight().contains(msg));
            assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
            assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
        },
        _ => {
            assert(s.in_flight().contains(msg));
            assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
            assert(s.controller_state == s_prime.controller_state);
            assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
        }
    }
}

}