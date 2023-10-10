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
    proof::{helper_invariants::*, predicate::*, resource::*},
    spec::{reconciler::*, resource::*, types::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

/// This function defined a replicas order for stateful set object. Here, obj can be the etcd statful set object, the object
/// in create/update stateful set object. We define this order because, the replicas in the update request is derived from
/// the triggering cr; so, in order to show the updated replicas is no smaller than the original one, we need to show that
/// the original one (the one stored in etcd)'s replicas is no larger than that of triggering cr. obj.metadata.owner_references_only_contains
/// (s.ongoing_reconciles()[key].triggering_cr.controller_owner_ref()) here is to ensure that the cr is still the one that creates the stateful
/// set object. The left two comparison is to assist the last one because when the state moves to the next state, the triggering_cr
/// may be assigned (inserted or updated).
spec fn replicas_satisfies_order(obj: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        obj.kind.is_StatefulSetKind(),
{
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let sts_replicas = replicas_of_stateful_set(obj);
        &&& s.resources().contains_key(key)
            && obj.metadata.owner_references_only_contains(RabbitmqClusterView::unmarshal(s.resources()[key]).get_Ok_0().controller_owner_ref())
            ==> sts_replicas <= replicas_of_rabbitmq(s.resources()[key])
        &&& s.scheduled_reconciles().contains_key(key)
            && obj.metadata.owner_references_only_contains(s.scheduled_reconciles()[key].controller_owner_ref())
            ==> sts_replicas <= s.scheduled_reconciles()[key].spec.replicas
        &&& s.ongoing_reconciles().contains_key(key)
            && obj.metadata.owner_references_only_contains(s.ongoing_reconciles()[key].triggering_cr.controller_owner_ref())
            ==> sts_replicas <= s.ongoing_reconciles()[key].triggering_cr.spec.replicas
    }
}

spec fn replicas_of_rabbitmq(obj: DynamicObjectView) -> int
    recommends
        obj.kind.is_CustomResourceKind(),
{
    RabbitmqClusterView::unmarshal(obj).get_Ok_0().spec.replicas
}

spec fn replicas_of_stateful_set(obj: DynamicObjectView) -> int
    recommends
        obj.kind.is_StatefulSetKind(),
{
    StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0()
}

spec fn replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq);
        forall |msg: RMQMessage|
            #[trigger] s.in_flight().contains(msg)
            ==> (
                resource_create_request_msg(sts_key)(msg)
                ==> replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s)
            ) && (
                resource_update_request_msg(sts_key)(msg)
                ==> replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s)
            )
    }
}

proof fn replicas_of_stateful_set_update_request_msg_satisfies_order_induction(
    rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster, msg: RMQMessage
)
    requires
        rabbitmq.well_formed(),
        RMQCluster::next()(s, s_prime),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s_prime),
        RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        RMQCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(rabbitmq)(s),
        object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(SubResource::StatefulSet, rabbitmq)(s),
        replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq)(s),
        s_prime.in_flight().contains(msg),
        resource_update_request_msg(make_stateful_set_key(rabbitmq))(msg),
    ensures
        replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime),
{
    let step = choose |step| RMQCluster::next_step(s, s_prime, step);
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(rabbitmq);
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
                    assert(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(SubResource::StatefulSet, rabbitmq)(s));
                    assert(get_request(SubResource::StatefulSet, rabbitmq).key == sts_key);
                    assert(owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1);
                    assert(owner_refs.get_Some_0()[0].uid < s.kubernetes_api_state.uid_counter);
                    assert(owner_refs.get_Some_0()[0] != RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                    assert(!msg.content.get_update_request().obj.metadata.owner_references_only_contains(RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref()));
                }
                assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
            }
            assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
        },
        Step::ControllerStep(input) => {
            if !s.in_flight().contains(msg) {
                StatefulSetView::marshal_preserves_integrity();
                StatefulSetView::marshal_spec_preserves_integrity();
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(SubResource::StatefulSet, rabbitmq, s, s_prime, msg, step);
                let triggering_cr = s.ongoing_reconciles()[key].triggering_cr;
                assert(StatefulSetView::unmarshal(msg.content.get_update_request().obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() == triggering_cr.spec.replicas);
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
            assume(s.kubernetes_api_state == s_prime.kubernetes_api_state);
            assert(s.controller_state == s_prime.controller_state);
            assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
        }
    }
}

}
