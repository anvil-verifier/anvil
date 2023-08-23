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
    proof::{common::*, liveness::helper_invariants::invariants::*},
    spec::{rabbitmqcluster::*, reconciler::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

spec fn stateful_set_not_scaled_down(rabbitmq: RabbitmqClusterView) -> ActionPred<RMQCluster> {
    |s: RMQCluster, s_prime: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        &&& s.resource_key_exists(sts_key)
        &&& s_prime.resource_key_exists(sts_key)
        ==> replicas_of_stateful_set(s_prime.resource_obj_of(sts_key)) >= replicas_of_stateful_set(s.resource_obj_of(sts_key))
    }
}

#[verifier(external_body)]
proof fn stateful_set_never_scaled_down_for_all()
    ensures
        forall |rabbitmq: RabbitmqClusterView|
            cluster_spec().entails(lift_action(#[trigger] stateful_set_not_scaled_down(rabbitmq))),
{}

spec fn replicas_of_rabbitmq(obj: DynamicObjectView) -> int
    recommends
        obj.kind.is_CustomResourceKind(),
{
    RabbitmqClusterView::from_dynamic_object(obj).get_Ok_0().spec.replicas
}

spec fn replicas_of_stateful_set(obj: DynamicObjectView) -> int
    recommends
        obj.kind.is_StatefulSetKind(),
{
    StatefulSetView::from_dynamic_object(obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0()
}

// Comparing replicas number
// resource_obj_of(sts_key) <= create/update_sts <= triggering_cr_of(cr_key) <= scheduled_cr_of(cr_key) <= resource_obj_of(cr_key)

spec fn scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.reconcile_scheduled_for(rabbitmq.object_ref())
        && s.resource_key_exists(rabbitmq.object_ref())
        ==> s.reconcile_scheduled_obj_of(rabbitmq.object_ref()).spec.replicas <= replicas_of_rabbitmq(s.resource_obj_of(rabbitmq.object_ref()))
    }
}

#[verifier(external_body)]
proof fn lemma_always_scheduled_cr_has_no_larger_replicas_than_current_cr(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq)))),
{}

spec fn triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.reconcile_state_contains(rabbitmq.object_ref())
        && s.resource_key_exists(rabbitmq.object_ref())
        ==> s.triggering_cr_of(rabbitmq.object_ref()).spec.replicas <= replicas_of_rabbitmq(s.resource_obj_of(rabbitmq.object_ref()))
    }
}

spec fn triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.reconcile_state_contains(rabbitmq.object_ref())
        && s.reconcile_scheduled_for(rabbitmq.object_ref())
        ==> s.triggering_cr_of(rabbitmq.object_ref()).spec.replicas <= s.reconcile_scheduled_obj_of(rabbitmq.object_ref()).spec.replicas
    }
}

#[verifier(external_body)]
proof fn lemma_always_triggering_cr_has_no_larger_replicas_than_current_cr(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)))),
{}

spec fn response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    let key = rabbitmq.object_ref();
    |s: RMQCluster| {
        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterGetStatefulSet)(s)
        ==> is_get_stateful_set_request(s.pending_req_of(key).content.get_APIRequest_0(), rabbitmq)
            && (
                forall |msg: Message|
                    #[trigger] s.message_in_flight(msg)
                    && resp_msg_matches_req_msg(msg, s.pending_req_of(key))
                    ==> sts_get_response_msg(key)(msg)
            )
    }
}

#[verifier(external_body)]
proof fn lemma_always_response_at_after_get_stateful_set_step_is_sts_get_response(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
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
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        // &&& RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(key, RabbitmqReconcileState {reconcile_step: RabbitmqReconcileStep::AfterGetStatefulSet})(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    RMQCluster::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if at_rabbitmq_step(key, RabbitmqReconcileStep::AfterGetStatefulSet)(s_prime) {
            if at_rabbitmq_step(key, RabbitmqReconcileStep::AfterGetStatefulSet)(s) {
                assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                assert(is_get_stateful_set_request(s_prime.pending_req_of(key).content.get_APIRequest_0(), rabbitmq));
            } else {
                assert(is_get_stateful_set_request(s_prime.pending_req_of(key).content.get_APIRequest_0(), rabbitmq));
            }
            assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && resp_msg_matches_req_msg(msg, s_prime.pending_req_of(key))
            implies sts_get_response_msg(key)(msg) by {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        assert(s.message_in_flight(msg));
                        let cr_key = input.2.get_Some_0();
                        if cr_key == key {
                            assert(s.message_in_flight(msg));
                            assert(false);
                        } else {
                            assert(s.pending_req_of(key) == s_prime.pending_req_of(key));
                            assert(sts_get_response_msg(key)(msg));
                        }
                    },
                    Step::KubernetesAPIStep(input) => {
                        assert(s.pending_req_of(key) == s_prime.pending_req_of(key));
                        if !s.message_in_flight(msg) {
                            assert(is_get_stateful_set_request(s_prime.pending_req_of(key).content.get_APIRequest_0(), rabbitmq));
                            assert(msg.content.is_get_response());
                            assert(msg == RMQCluster::handle_get_request(s.pending_req_of(key), s.kubernetes_api_state).1);
                            assert(sts_get_response_msg(key)(msg));
                        }
                    },
                    _ => {}
                }
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

spec fn stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        let etcd_rv = s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0();
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            ==> (
                    sts_update_request_msg(rabbitmq.object_ref())(msg)
                    ==> msg.content.get_update_request().obj.metadata.resource_version.is_Some()
                        && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() <= s.kubernetes_api_state.resource_version_counter
                        && (s.resource_key_exists(sts_key) ==> msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() <= etcd_rv)
                ) && (
                    ok_sts_get_response_msg(rabbitmq.object_ref())(msg)
                    ==> msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
                        && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() <= s.kubernetes_api_state.resource_version_counter
                        && (s.resource_key_exists(sts_key) ==> msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() <= etcd_rv)
                )
    }
}

proof fn lemma_always_stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(rabbitmq)))),
{
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(rabbitmq.object_ref());
    let upd_rv_leq = |msg: Message, s: RMQCluster| {
        sts_update_request_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_update_request().obj.metadata.resource_version.is_Some()
            && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() <= s.kubernetes_api_state.resource_version_counter
            && (s.resource_key_exists(sts_key) ==> msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() <= s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0())
    };
    let get_rv_leq = |msg: Message, s: RMQCluster| {
        ok_sts_get_response_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
            && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() <= s.kubernetes_api_state.resource_version_counter
            && (s.resource_key_exists(sts_key) ==> msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() <= s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0())
    };
    let inv = stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq)(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    lemma_always_response_at_after_get_stateful_set_step_is_sts_get_response(spec, rabbitmq);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()), 
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        lift_state(response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq)),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let etcd_rv = s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0();
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) implies upd_rv_leq(msg, s_prime) && get_rv_leq(msg, s_prime) by {
            let step = choose |step| RMQCluster::next_step(s, s_prime, step);
            if s.message_in_flight(msg) {
                assert(s.kubernetes_api_state.resource_version_counter <= s_prime.kubernetes_api_state.resource_version_counter);
                if !s.resource_key_exists(sts_key) {
                    if s_prime.resource_key_exists(sts_key) {
                        assert(s_prime.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == s.kubernetes_api_state.resource_version_counter);
                    }
                    assert(upd_rv_leq(msg, s_prime));
                    assert(get_rv_leq(msg, s_prime));
                } else {
                    if s_prime.resource_key_exists(sts_key) {
                        assert(s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() <= s_prime.resource_obj_of(sts_key).metadata.resource_version.get_Some_0());
                    }
                    assert(upd_rv_leq(msg, s_prime));
                    assert(get_rv_leq(msg, s_prime));
                }
            } else if sts_update_request_msg(rabbitmq.object_ref())(msg) {
                lemma_stateful_set_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                // assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterGetStatefulSet)(s) || at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s));
                assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s_prime));
                // assert(
                //     exists |msg| 
                //         #[trigger] s.message_in_flight(msg)
                //         && ok_sts_get_response_msg(rabbitmq.object_ref())(msg) 
                //         && msg.content.get_update_request().obj == update_stateful_set(rabbitmq, StatefulSetView::from_dynamic_object(msg.content.get_get_response().res.get_Ok_0()).get_Ok_0()).to_dynamic_object()
                // );
                assert(upd_rv_leq(msg, s_prime));
                assert(get_rv_leq(msg, s_prime));
            } else if ok_sts_get_response_msg(rabbitmq.object_ref())(msg) {
                let input = step.get_KubernetesAPIStep_0().get_Some_0();
                assert(msg == RMQCluster::handle_get_request(input, s.kubernetes_api_state).1);
                assert(input.content.is_get_request());
                assert(s.resource_key_exists(input.content.get_get_request().key));
                assert(input.content.get_get_request().key == msg.content.get_get_response().res.get_Ok_0().object_ref());
                assert(input.content.get_get_request().key == sts_key);
                assert(s.resource_obj_of(sts_key).object_ref() == sts_key);
                assert(s.resource_key_exists(sts_key));
                assert(msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() == s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0());
                assert(get_rv_leq(msg, s_prime));
                assert(upd_rv_leq(msg, s_prime));
            } else {
                assert(get_rv_leq(msg, s_prime));
                assert(upd_rv_leq(msg, s_prime));
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

// We have to show current sts obj has no larger replicas than triggering cr, because that is how the update messgae is created.
// The other to <= are used to make the triggering_cr invariant hold (easier to prove)
spec fn replicas_satisfies_order(obj: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        obj.kind.is_StatefulSetKind(),
{
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let sts_replicas = replicas_of_stateful_set(obj);
        &&& s.resource_key_exists(key)
            && obj.metadata.owner_references_only_contains(RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).get_Ok_0().controller_owner_ref())
            ==> sts_replicas <= replicas_of_rabbitmq(s.resource_obj_of(key))
        &&& s.reconcile_scheduled_for(key)
            && obj.metadata.owner_references_only_contains(s.reconcile_scheduled_obj_of(key).controller_owner_ref())
            ==> sts_replicas <= s.reconcile_scheduled_obj_of(key).spec.replicas
        &&& s.reconcile_state_contains(key)
            && obj.metadata.owner_references_only_contains(s.triggering_cr_of(key).controller_owner_ref())
            ==> sts_replicas <= s.triggering_cr_of(key).spec.replicas
    }
}

spec fn replicas_of_etcd_stateful_set_satisfies_order(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let sts_key = make_stateful_set_key(key);
        s.resource_key_exists(sts_key) ==> replicas_satisfies_order(s.resource_obj_of(sts_key), rabbitmq)(s)
    }
}

// show that update msg resource version <= s.resource_obj_of(sts_key) resource version
spec fn replicas_of_stateful_set_update_request_msg_satisfies_order(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            && sts_update_request_msg(rabbitmq.object_ref())(msg)
            ==> replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s)
    }
}

// show that create msg resource version <= s.resource_obj_of(sts_key) resource version
spec fn replicas_of_stateful_set_create_request_msg_satisfies_order(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            && sts_create_request_msg(rabbitmq.object_ref())(msg)
            ==> replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s)
    }
}

// if the resource versions do not equal when created, it will never equal each other
spec fn replicas_of_stateful_set_update_request_msg_is_no_larger_than_etcd(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            && sts_update_request_msg(rabbitmq.object_ref())(msg)
            && s.resource_key_exists(sts_key)
            && s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == msg.content.get_update_request().obj.metadata.resource_version.get_Some_0()
            ==> StatefulSetView::from_dynamic_object(s.resource_obj_of(sts_key)).get_Ok_0().spec.get_Some_0().replicas.get_Some_0()
                <= replicas_of_stateful_set(msg.content.get_create_request().obj)
    }
}

proof fn helper_1(rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster)
    requires
        RMQCluster::next()(s, s_prime),
        replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)(s),
        replicas_of_stateful_set_update_request_msg_satisfies_order(rabbitmq)(s),
        replicas_of_stateful_set_create_request_msg_satisfies_order(rabbitmq)(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
        every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter()(s),
    ensures
        replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)(s_prime),
{
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(key);
    if s_prime.resource_key_exists(sts_key) {
        if s.resource_key_exists(sts_key) && s.resource_obj_of(sts_key) == s_prime.resource_obj_of(sts_key) {
            if s_prime.resource_key_exists(key) {
                if !s.resource_key_exists(key) {
                    assert(s_prime.resource_obj_of(key).metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                    let owner_refs = s.resource_obj_of(sts_key).metadata.owner_references;
                    if owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1 {
                        assert(owner_refs.get_Some_0()[0].uid != s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).get_Ok_0().controller_owner_ref());
                    }
                } else if s.resource_obj_of(key) != s_prime.resource_obj_of(key) {
                    assert(s.resource_obj_of(key).metadata.uid == s_prime.resource_obj_of(key).metadata.uid);
                    assert(RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).is_Ok());
                    assert(RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).is_Ok());
                    assert(RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).get_Ok_0().controller_owner_ref() == RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).get_Ok_0().controller_owner_ref());
                    assert(replicas_of_rabbitmq(s.resource_obj_of(key)) <= replicas_of_rabbitmq(s_prime.resource_obj_of(key)));
                }
            }
            if s_prime.reconcile_scheduled_for(key) {
                if !s.reconcile_scheduled_for(key) || s.reconcile_scheduled_obj_of(key) != s_prime.reconcile_scheduled_obj_of(key) {
                    assert(s_prime.reconcile_scheduled_obj_of(key) == RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).get_Ok_0());
                }
            }
            if s_prime.reconcile_state_contains(key) {
                if !s.reconcile_state_contains(key) || s.triggering_cr_of(key) != s_prime.triggering_cr_of(key) {
                    assert(s_prime.triggering_cr_of(key) == s.reconcile_scheduled_obj_of(key));
                }
            }
        } else if s.resource_key_exists(sts_key) && s.resource_obj_of(sts_key) != s_prime.resource_obj_of(sts_key) {
            assert(replicas_of_stateful_set_update_request_msg_satisfies_order(rabbitmq)(s));
            assert(replicas_satisfies_order(s_prime.resource_obj_of(sts_key), rabbitmq)(s_prime));
        } else {
            assert(replicas_of_stateful_set_create_request_msg_satisfies_order(rabbitmq)(s));
            assert(replicas_satisfies_order(s_prime.resource_obj_of(sts_key), rabbitmq)(s_prime));
        }
    } 
}

spec fn every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter() -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |key|
            #[trigger] s.resource_key_exists(key)
            && s.resource_obj_of(key).metadata.owner_references.is_Some()
            ==> {
                let owner_refs = s.resource_obj_of(key).metadata.owner_references.get_Some_0();
                forall |i| 
                    #![auto] 0 <= i < owner_refs.len() 
                    ==> owner_refs[i].uid != s.kubernetes_api_state.uid_counter
            }
    }
}

#[verifier(external_body)]
proof fn lemma_always_replicas_of_etcd_stateful_set_satisfies_order(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)))),
{
    let inv = replicas_of_etcd_stateful_set_satisfies_order(rabbitmq);
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s)
        &&& triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s)
    };
    lemma_always_scheduled_cr_has_no_larger_replicas_than_current_cr(spec, rabbitmq);
    lemma_always_triggering_cr_has_no_larger_replicas_than_current_cr(spec, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq)),
        lift_state(triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        let key = rabbitmq.object_ref();
        let sts_key = make_stateful_set_key(key);
        if s_prime.resource_key_exists(sts_key) {
            match step {
                Step::KubernetesAPIStep(input) => {
                    assert(s.controller_state == s_prime.controller_state);
                    if s.resource_key_exists(sts_key) {} else {}
                },
                _ => {}
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), stronger_next, inv);
}

}
