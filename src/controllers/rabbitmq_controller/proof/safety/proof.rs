// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::vstatefulset_controller::trusted::spec_types::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::{reconciler::*, resource::*},
    proof::{helper_invariants::*, predicate::*, resource::*},
    trusted::{safety_theorem::*, spec_types::*, step::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

proof fn safety_proof_forall_rabbitmq(controller_id: int, cluster: Cluster)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures safety_theorem(cluster),
{
    assert forall |rabbitmq: RabbitmqClusterView| #[trigger] cluster_spec_without_wf(cluster).entails(safety(rabbitmq)) by {
        safety_proof(controller_id, cluster, rabbitmq);
    };
    spec_entails_tla_forall(cluster_spec_without_wf(cluster), |rabbitmq: RabbitmqClusterView| safety(rabbitmq));
}

proof fn safety_proof(controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures cluster_spec_without_wf(cluster).entails(safety(rabbitmq)),
{
    lemma_stateful_set_never_scaled_down_for_rabbitmq(controller_id, cluster, cluster_spec_without_wf(cluster), rabbitmq);
}

// This invariant is exactly the high-level property. The proof of this invariant is where we talk about update Message. It requires another two invariants to hold all the time:
// - replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd
// - object_in_sts_update_request_has_smaller_rv_than_etcd
//
// Invariant 2 is to show that every stateful set update request must specify the resource version because stateful set is allowed to update unconditionally. If resource version can be none, we can't rule out invalid update request through resource version. Invariant 3 is quite obvious.
proof fn lemma_stateful_set_never_scaled_down_for_rabbitmq(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_action(stateful_set_not_scaled_down(rabbitmq)))),
{
    let inv = stateful_set_not_scaled_down(rabbitmq);
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
    };
    lemma_always_replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(controller_id, cluster, spec, rabbitmq);
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    assert forall |s, s_prime| #[trigger] next(s, s_prime) implies stateful_set_not_scaled_down(rabbitmq)(s, s_prime) by {
        let sts_key = make_stateful_set_key(rabbitmq);
        if s.resources().contains_key(sts_key) && s_prime.resources().contains_key(sts_key) {
            if s.resources()[sts_key].spec != s_prime.resources()[sts_key].spec {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                let input = step->APIServerStep_0->0;
                if input.content.is_delete_request() {
                    assert(VStatefulSetView::unmarshal(s.resources()[sts_key])->Ok_0.spec == VStatefulSetView::unmarshal(s_prime.resources()[sts_key])->Ok_0.spec);
                } else {
                    if resource_get_then_update_request_msg(sts_key)(input) {} else {}
                    assert(s.resources()[sts_key].metadata.resource_version->0 == input.content.get_get_then_update_request().obj.metadata.resource_version->0);
                    assert(replicas_of_stateful_set(s_prime.resources()[sts_key]) == replicas_of_stateful_set(input.content.get_get_then_update_request().obj));
                    assert(replicas_of_stateful_set(s_prime.resources()[sts_key]) >= replicas_of_stateful_set(s.resources()[sts_key]));
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(next), lift_action(inv),
        lift_action(cluster.next()), lift_state(replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()), later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))
    );
}

spec fn replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let sts_key = make_stateful_set_key(rabbitmq);
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg)
            && resource_get_then_update_request_msg(sts_key)(msg)
            && s.resources().contains_key(sts_key)
            && s.resources()[sts_key].metadata.resource_version->0 == msg.content.get_get_then_update_request().obj.metadata.resource_version->0
            ==> replicas_of_stateful_set(s.resources()[sts_key]) <= replicas_of_stateful_set(msg.content.get_get_then_update_request().obj)
    }
}

proof fn lemma_always_replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)))),
{
    let inv = replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq);
    // let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(rabbitmq);
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& replicas_of_etcd_stateful_set_satisfies_order(controller_id, rabbitmq)(s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)(s)
        &&& response_at_after_get_resource_step_is_resource_get_response(controller_id, SubResource::VStatefulSetView, rabbitmq)(s)
    };
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    lemma_always_replicas_of_etcd_stateful_set_satisfies_order(controller_id, cluster, spec, rabbitmq);
    always_to_always_later(spec, lift_state(replicas_of_etcd_stateful_set_satisfies_order(controller_id, rabbitmq)));
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, sts_key);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(controller_id, cluster, spec, SubResource::VStatefulSetView, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()), later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        later(lift_state(replicas_of_etcd_stateful_set_satisfies_order(controller_id, rabbitmq))),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, SubResource::VStatefulSetView, rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && resource_get_then_update_request_msg(sts_key)(msg) && s_prime.resources().contains_key(sts_key)
        && s_prime.resources()[sts_key].metadata.resource_version->0 == msg.content.get_get_then_update_request().obj.metadata.resource_version->0
        implies VStatefulSetView::unmarshal(s_prime.resources()[sts_key])->Ok_0.spec.replicas->0
        <= replicas_of_stateful_set(msg.content.get_get_then_update_request().obj) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                if !s.resources().contains_key(sts_key) || s.resources()[sts_key] != s_prime.resources()[sts_key] {
                    assert(s_prime.resources()[sts_key].metadata.resource_version->0 == s.api_server.resource_version_counter);
                    assert(msg.content.get_get_then_update_request().obj.metadata.resource_version->0 < s.api_server.resource_version_counter);
                    assert(false);
                } else {
                    assert(VStatefulSetView::unmarshal(s_prime.resources()[sts_key])->Ok_0.spec.replicas->0 <= replicas_of_stateful_set(msg.content.get_get_then_update_request().obj));
                }
            } else {
                VStatefulSetView::marshal_preserves_integrity();
                VStatefulSetView::marshal_spec_preserves_integrity();
                lemma_resource_get_then_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, SubResource::VStatefulSetView, rabbitmq, s, s_prime, msg, step);
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

// This function defined a replicas order for stateful set object. Here, obj can be the etcd statful set object, the object
// in create/update stateful set object. We define this order because, the replicas in the update request is derived from
// the triggering cr; so, in order to show the updated replicas is no smaller than the original one, we need to show that
// the original one (the one stored in etcd)'s replicas is no larger than that of triggering cr. obj.metadata.owner_references_only_contains
// (s.ongoing_reconciles(controller_id)[key].triggering_cr.controller_owner_ref()) here is to ensure that the cr is still the one that creates the stateful
// set object. The left two comparison is to assist the last one because when the state moves to the next state, the triggering_cr
// may be assigned (inserted or updated).
spec fn replicas_satisfies_order(controller_id: int, obj: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState>
    recommends
        obj.kind is StatefulSetKind,
{
    |s: ClusterState| {
        let key = rabbitmq.object_ref();
        let sts_replicas = replicas_of_stateful_set(obj);
        &&& s.resources().contains_key(key)
            && obj.metadata.owner_references_only_contains(RabbitmqClusterView::unmarshal(s.resources()[key])->Ok_0.controller_owner_ref())
            ==> sts_replicas <= replicas_of_rabbitmq(s.resources()[key])
        &&& s.scheduled_reconciles(controller_id).contains_key(key)
            && obj.metadata.owner_references_only_contains(RabbitmqClusterView::unmarshal(s.scheduled_reconciles(controller_id)[key]).unwrap().controller_owner_ref())
            ==> sts_replicas <= RabbitmqClusterView::unmarshal(s.scheduled_reconciles(controller_id)[key]).unwrap().spec().replicas
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
            && obj.metadata.owner_references_only_contains(RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap().controller_owner_ref())
            ==> sts_replicas <= RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap().spec().replicas
    }
}

spec fn replicas_of_rabbitmq(obj: DynamicObjectView) -> int
    recommends
        obj.kind is CustomResourceKind,
{
    RabbitmqClusterView::unmarshal(obj)->Ok_0.spec.replicas
}

spec fn replicas_of_etcd_stateful_set_satisfies_order(controller_id: int, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let sts_key = make_stateful_set_key(rabbitmq);
        s.resources().contains_key(sts_key) ==> replicas_satisfies_order(controller_id, s.resources()[sts_key], rabbitmq)(s)
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_always_replicas_of_etcd_stateful_set_satisfies_order(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(replicas_of_etcd_stateful_set_satisfies_order(controller_id, rabbitmq)))),
{
    let inv = replicas_of_etcd_stateful_set_satisfies_order(controller_id, rabbitmq);
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(controller_id, rabbitmq)(s)
        &&& no_create_resource_request_msg_without_name_in_flight(SubResource::VStatefulSetView, rabbitmq)(s)
    };
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(controller_id, cluster, spec, SubResource::VStatefulSetView, rabbitmq);
    lemma_always_replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(controller_id, cluster, spec, rabbitmq);
    lemma_always_no_create_resource_request_msg_without_name_in_flight(cluster, controller_id, spec, SubResource::VStatefulSetView, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()), lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(controller_id, rabbitmq)),
        lift_state(no_create_resource_request_msg_without_name_in_flight(SubResource::VStatefulSetView, rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = rabbitmq.object_ref();
        let sts_key = make_stateful_set_key(rabbitmq);
        if s_prime.resources().contains_key(sts_key) {
            if s.resources().contains_key(sts_key) && s.resources()[sts_key] == s_prime.resources()[sts_key] {
                if s_prime.resources().contains_key(key) {
                    if !s.resources().contains_key(key) {
                        assert(s_prime.resources()[key].metadata.uid->0 == s.api_server.uid_counter);
                        let owner_refs = s.resources()[sts_key].metadata.owner_references;
                        assert(owner_refs->0[0].uid != s.api_server.uid_counter);
                        assert(owner_refs->0[0] != RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0.controller_owner_ref());
                    } else if s.resources()[key] != s_prime.resources()[key] {
                        assert(s.resources()[key].metadata.uid == s_prime.resources()[key].metadata.uid);
                        assert(RabbitmqClusterView::unmarshal(s.resources()[key])->Ok_0.controller_owner_ref() == RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0.controller_owner_ref());
                        assert(replicas_of_rabbitmq(s.resources()[key]) <= replicas_of_rabbitmq(s_prime.resources()[key]));
                    }
                }
            } else {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        let req = input->0;
                        assert(!resource_create_request_msg_without_name(sts_key.kind, sts_key.namespace)(req));
                    },
                    _ => {},
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

spec fn replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(controller_id: int, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let sts_key = make_stateful_set_key(rabbitmq);
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg)
            ==> (
                resource_create_request_msg(sts_key)(msg)
                ==> replicas_satisfies_order(controller_id, msg.content.get_create_request().obj, rabbitmq)(s)
            ) && (
                resource_get_then_update_request_msg(sts_key)(msg)
                ==> replicas_satisfies_order(controller_id, msg.content.get_get_then_update_request().obj, rabbitmq)(s)
            )
    }
}

proof fn lemma_always_replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(controller_id, rabbitmq)))),
{
    let inv = replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(controller_id, rabbitmq);
    let sts_key = make_stateful_set_key(rabbitmq);
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(controller_id, rabbitmq)(s)
        &&& object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(SubResource::VStatefulSetView, rabbitmq)(s)
    };
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(spec, controller_id, rabbitmq);
    lemma_always_object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(controller_id, cluster, spec, SubResource::VStatefulSetView, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(cluster.next()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(controller_id, rabbitmq)),
        lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(SubResource::VStatefulSetView, rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) implies (resource_create_request_msg(sts_key)(msg)
        ==> replicas_satisfies_order(controller_id, msg.content.get_create_request().obj, rabbitmq)(s_prime)) && (resource_get_then_update_request_msg(sts_key)(msg)
        ==> replicas_satisfies_order(controller_id, msg.content.get_get_then_update_request().obj, rabbitmq)(s_prime)) by {
            if resource_create_request_msg(sts_key)(msg) {
                replicas_of_stateful_set_create_request_msg_satisfies_order_induction(controller_id, cluster, rabbitmq, s, s_prime, msg);
            }
            if resource_get_then_update_request_msg(sts_key)(msg) {
                replicas_of_stateful_set_update_request_msg_satisfies_order_induction(controller_id, cluster, rabbitmq, s, s_prime, msg);
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

proof fn replicas_of_stateful_set_create_request_msg_satisfies_order_induction(
    controller_id: int,
    cluster: Cluster, rabbitmq: RabbitmqClusterView, s: ClusterState, s_prime: ClusterState, msg: Message
)
    requires
        cluster.next()(s, s_prime),
        cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s),
        cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        Cluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(controller_id, rabbitmq)(s),
        object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(SubResource::VStatefulSetView, rabbitmq)(s),
        replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(controller_id, rabbitmq)(s),
        s_prime.in_flight().contains(msg),
        resource_create_request_msg(make_stateful_set_key(rabbitmq))(msg),
    ensures replicas_satisfies_order(controller_id, msg.content.get_create_request().obj, rabbitmq)(s_prime),
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(rabbitmq);
    match step {
        Step::APIServerStep(input) => {
            assert(s.controller_and_externals == s_prime.controller_and_externals);
            assert(s.in_flight().contains(msg));
            if s_prime.resources().contains_key(key) {
                if s.resources().contains_key(key) {
                    assert(replicas_of_rabbitmq(s.resources()[key]) <= replicas_of_rabbitmq(s_prime.resources()[key]));
                } else {
                    let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
                    assert(owner_refs is Some && owner_refs->0.len() == 1);
                    assert(owner_refs->0[0].uid < s.api_server.uid_counter);
                    assert(owner_refs->0[0] != RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0.controller_owner_ref());
                    assert(!msg.content.get_create_request().obj.metadata.owner_references_only_contains(RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0.controller_owner_ref()));
                }
            }
        },
        Step::ControllerStep(input) => {
            if !s.in_flight().contains(msg) {
                VStatefulSetView::marshal_preserves_integrity();
                VStatefulSetView::marshal_spec_preserves_integrity();
                lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, SubResource::VStatefulSetView, rabbitmq, s, s_prime, msg, step);
            }
        },
        _ => {
            assert(s.in_flight().contains(msg));
            assert(s.resources().contains_key(key) == s_prime.resources().contains_key(key));
            if s.resources().contains_key(key) {
                assert(s.resources()[key] == s_prime.resources()[key]);
            }
        },
    }
}

proof fn replicas_of_stateful_set_update_request_msg_satisfies_order_induction(
    controller_id: int,
    cluster: Cluster, rabbitmq: RabbitmqClusterView, s: ClusterState, s_prime: ClusterState, msg: Message
)
    requires
        cluster.next()(s, s_prime),
        cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s),
        cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        Cluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(controller_id, rabbitmq)(s),
        object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(SubResource::VStatefulSetView, rabbitmq)(s),
        // no_create_resource_request_msg_without_name_in_flight(SubResource::VStatefulSetView, rabbitmq)(s),
        replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(controller_id, rabbitmq)(s),
        s_prime.in_flight().contains(msg),
        resource_get_then_update_request_msg(make_stateful_set_key(rabbitmq))(msg),
    ensures replicas_satisfies_order(controller_id, msg.content.get_get_then_update_request().obj, rabbitmq)(s_prime),
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(rabbitmq);
    match step {
        Step::APIServerStep(input) => {
            assert(s.in_flight().contains(msg));
            assert(s.controller_and_externals == s_prime.controller_and_externals);
            if s_prime.resources().contains_key(key) {
                if s.resources().contains_key(key) {
                    assert(replicas_of_rabbitmq(s.resources()[key]) <= replicas_of_rabbitmq(s_prime.resources()[key]));
                } else {
                    let owner_refs = msg.content.get_get_then_update_request().obj.metadata.owner_references;
                    assert(owner_refs is Some && owner_refs->0.len() == 1);
                    assert(owner_refs->0[0].uid < s.api_server.uid_counter);
                    assert(owner_refs->0[0] != RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0.controller_owner_ref());
                    assert(!msg.content.get_get_then_update_request().obj.metadata.owner_references_only_contains(RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0.controller_owner_ref()));
                }
            }
        },
        Step::ControllerStep(input) => {
            if !s.in_flight().contains(msg) {
                VStatefulSetView::marshal_preserves_integrity();
                VStatefulSetView::marshal_spec_preserves_integrity();
                lemma_resource_get_then_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, SubResource::VStatefulSetView, rabbitmq, s, s_prime, msg, step);
            }
        },
        _ => {
            assert(s.in_flight().contains(msg));
            assert(s.resources().contains_key(key) == s_prime.resources().contains_key(key));
            if s.resources().contains_key(key) {
                assert(s.resources()[key] == s_prime.resources()[key]);
            }
        },
    }
}

}
