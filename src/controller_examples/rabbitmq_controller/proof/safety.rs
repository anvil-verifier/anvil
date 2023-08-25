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
        s.resource_key_exists(sts_key)
        && s_prime.resource_key_exists(sts_key)
        ==> replicas_of_stateful_set(s_prime.resource_obj_of(sts_key)) >= replicas_of_stateful_set(s.resource_obj_of(sts_key))
    }
}

proof fn lemma_stateful_set_never_scaled_down_for_all(spec: TempPred<RMQCluster>)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        forall |rabbitmq: RabbitmqClusterView|
            spec.entails(always(lift_action(#[trigger] stateful_set_not_scaled_down(rabbitmq)))),
{
    assert forall |rabbitmq| spec.entails(always(lift_action(#[trigger] stateful_set_not_scaled_down(rabbitmq)))) by {
        lemma_stateful_set_never_scaled_down_for_rabbitmq(spec, rabbitmq);
    }
}

proof fn lemma_stateful_set_never_scaled_down_for_rabbitmq(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_action(stateful_set_not_scaled_down(rabbitmq)))),
{
    let inv = stateful_set_not_scaled_down(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)(s)
        &&& stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(rabbitmq)(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
    };
    lemma_always_replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(spec, rabbitmq);
    lemma_always_stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(spec, rabbitmq);
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    assert forall |s, s_prime| #[trigger] next(s, s_prime) implies stateful_set_not_scaled_down(rabbitmq)(s, s_prime) by {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        if s.resource_key_exists(sts_key) && s_prime.resource_key_exists(sts_key) {
            if s.resource_obj_of(sts_key) != s_prime.resource_obj_of(sts_key) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                let input = step.get_KubernetesAPIStep_0().get_Some_0();
                if input.content.is_delete_request() {
                    assert(StatefulSetView::from_dynamic_object(s.resource_obj_of(sts_key)).get_Ok_0().spec == StatefulSetView::from_dynamic_object(s_prime.resource_obj_of(sts_key)).get_Ok_0().spec);
                } else {
                    assert(input.content.is_update_request());
                    assert(s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == input.content.get_update_request().obj.metadata.resource_version.get_Some_0());
                    assert(replicas_of_stateful_set(s_prime.resource_obj_of(sts_key)) == replicas_of_stateful_set(input.content.get_update_request().obj));
                    assert(replicas_of_stateful_set(s_prime.resource_obj_of(sts_key)) >= replicas_of_stateful_set(s.resource_obj_of(sts_key)));
                }
            } 
        }
    }
    invariant_n!(
        spec, lift_action(next), lift_action(inv),
        lift_action(RMQCluster::next()), lift_state(replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)),
        lift_state(stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(rabbitmq)),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()), later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))
    );
}

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
        && s.resource_obj_of(rabbitmq.object_ref()).metadata.uid.get_Some_0() == s.reconcile_scheduled_obj_of(rabbitmq.object_ref()).metadata.uid.get_Some_0()
        ==> s.reconcile_scheduled_obj_of(rabbitmq.object_ref()).spec.replicas <= replicas_of_rabbitmq(s.resource_obj_of(rabbitmq.object_ref()))
    }
}

proof fn lemma_always_scheduled_cr_has_no_larger_replicas_than_current_cr(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq)))),
{
    let inv = scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::scheduled_cr_has_lower_uid_than_uid_counter()(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    RMQCluster::lemma_always_scheduled_cr_has_lower_uid_than_uid_counter(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::scheduled_cr_has_lower_uid_than_uid_counter())
    );
    let key = rabbitmq.object_ref();
    assert forall |s, s_prime: RMQCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.reconcile_scheduled_for(key) && s_prime.resource_key_exists(key)
        && s_prime.resource_obj_of(rabbitmq.object_ref()).metadata.uid.get_Some_0() == s_prime.reconcile_scheduled_obj_of(rabbitmq.object_ref()).metadata.uid.get_Some_0() {
            let step = choose |step: RMQStep| RMQCluster::next_step(s, s_prime, step);
            match step {
                Step::KubernetesAPIStep(input) => {
                    assert(s.reconcile_scheduled_for(key) && s.reconcile_scheduled_obj_of(key) == s_prime.reconcile_scheduled_obj_of(key));
                    if !s.resource_key_exists(key) {
                        assert(s_prime.resource_obj_of(key).metadata.uid == Some(s.kubernetes_api_state.uid_counter));
                        assert(s_prime.resource_obj_of(rabbitmq.object_ref()).metadata.uid.get_Some_0() != s_prime.reconcile_scheduled_obj_of(rabbitmq.object_ref()).metadata.uid.get_Some_0());
                    } else if s.resource_obj_of(key) != s_prime.resource_obj_of(key) {
                        assert(RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).is_Ok());
                        assert(RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).is_Ok());
                        assert(replicas_of_rabbitmq(s.resource_obj_of(key)) <= replicas_of_rabbitmq(s_prime.resource_obj_of(key)));
                    }
                },
                Step::ScheduleControllerReconcileStep(input) => {
                    assert(s.resource_key_exists(key) && s.resource_obj_of(key) == s_prime.resource_obj_of(key));
                    if !s.reconcile_scheduled_for(key) || s.reconcile_scheduled_obj_of(key) != s_prime.reconcile_scheduled_obj_of(key) {
                        assert(s_prime.reconcile_scheduled_obj_of(rabbitmq.object_ref()).spec.replicas == replicas_of_rabbitmq(s_prime.resource_obj_of(rabbitmq.object_ref())));
                    }
                },
                _ => {}
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

spec fn triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.reconcile_state_contains(rabbitmq.object_ref())
        && s.resource_key_exists(rabbitmq.object_ref())
        && s.resource_obj_of(rabbitmq.object_ref()).metadata.uid.get_Some_0() == s.triggering_cr_of(rabbitmq.object_ref()).metadata.uid.get_Some_0()
        ==> s.triggering_cr_of(rabbitmq.object_ref()).spec.replicas <= replicas_of_rabbitmq(s.resource_obj_of(rabbitmq.object_ref()))
    }
}

spec fn triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.reconcile_state_contains(rabbitmq.object_ref())
        && s.reconcile_scheduled_for(rabbitmq.object_ref())
        && s.triggering_cr_of(rabbitmq.object_ref()).metadata.uid.get_Some_0() == s.reconcile_scheduled_obj_of(rabbitmq.object_ref()).metadata.uid.get_Some_0()
        ==> s.triggering_cr_of(rabbitmq.object_ref()).spec.replicas <= s.reconcile_scheduled_obj_of(rabbitmq.object_ref()).spec.replicas
    }
}

proof fn lemma_always_triggering_cr_has_no_larger_replicas_than_scheduled_cr_and_current_cr(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)))),
        spec.entails(always(lift_state(triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq)))),
{
    let inv = |s: RMQCluster| {
        &&& triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s)
        &&& triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq)(s)
    };
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::triggering_cr_has_lower_uid_than_uid_counter()(s)
        &&& scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    RMQCluster::lemma_always_triggering_cr_has_lower_uid_than_uid_counter(spec);
    lemma_always_scheduled_cr_has_no_larger_replicas_than_current_cr(spec, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::triggering_cr_has_lower_uid_than_uid_counter()),
        lift_state(scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        s_leq_both_to_s_prime_leq_scheduled_cr(rabbitmq, s, s_prime);
        s_leq_both_to_s_prime_leq_current_cr(rabbitmq, s, s_prime);
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
    always_weaken(spec, inv, triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq));
    always_weaken(spec, inv, triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq));
}

proof fn s_leq_both_to_s_prime_leq_scheduled_cr(rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster)
    requires
        RMQCluster::next()(s, s_prime),
        triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s),
        triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq)(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
    ensures
        triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq)(s_prime),
{}

proof fn s_leq_both_to_s_prime_leq_current_cr(rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster)
    requires
        RMQCluster::next()(s, s_prime),
        scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s),
        triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s),
        triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq)(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
        RMQCluster::triggering_cr_has_lower_uid_than_uid_counter()(s),
    ensures
        triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s_prime),
{
    let key = rabbitmq.object_ref();
    if s_prime.reconcile_state_contains(rabbitmq.object_ref()) && s_prime.resource_key_exists(rabbitmq.object_ref())
    && s_prime.resource_obj_of(rabbitmq.object_ref()).metadata.uid.get_Some_0() == s_prime.triggering_cr_of(rabbitmq.object_ref()).metadata.uid.get_Some_0() {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        if step.is_KubernetesAPIStep() {
            assert(s.reconcile_state_contains(key) && s.triggering_cr_of(key) == s_prime.triggering_cr_of(key));
            if !s.resource_key_exists(key) {
                assert(s_prime.resource_obj_of(key).metadata.uid == Some(s.kubernetes_api_state.uid_counter));
                assert(s_prime.resource_obj_of(rabbitmq.object_ref()).metadata.uid.get_Some_0() != s_prime.triggering_cr_of(rabbitmq.object_ref()).metadata.uid.get_Some_0());
            } else if s.resource_obj_of(key) != s_prime.resource_obj_of(key) {
                assert(RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).is_Ok());
                assert(RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).is_Ok());
                assert(replicas_of_rabbitmq(s.resource_obj_of(key)) <= replicas_of_rabbitmq(s_prime.resource_obj_of(key)));
            }
        } else if step.is_ControllerStep() {
            assert(s.resource_key_exists(key) && s.resource_obj_of(key) == s_prime.resource_obj_of(key));
            if !s.reconcile_state_contains(key) || s.triggering_cr_of(key) != s_prime.triggering_cr_of(key) {
                assert(s_prime.triggering_cr_of(rabbitmq.object_ref()).spec.replicas == s.reconcile_scheduled_obj_of(rabbitmq.object_ref()).spec.replicas);
            }
        }
    }
}

spec fn response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    let key = rabbitmq.object_ref();
    |s: RMQCluster| {
        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterGetStatefulSet)(s)
        ==> s.reconcile_state_of(key).pending_req_msg.is_Some()
            && is_get_stateful_set_request(s.pending_req_of(key).content.get_APIRequest_0(), rabbitmq)
            && (
                forall |msg: Message|
                    #[trigger] s.message_in_flight(msg)
                    && resp_msg_matches_req_msg(msg, s.pending_req_of(key))
                    ==> sts_get_response_msg(key)(msg)
            )
    }
}

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
        &&& RMQCluster::every_in_flight_or_pending_req_msg_has_unique_id()(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    RMQCluster::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    RMQCluster::lemma_always_every_in_flight_or_pending_req_msg_has_unique_id(spec);
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(RMQCluster::every_in_flight_or_pending_req_msg_has_unique_id()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if at_rabbitmq_step(key, RabbitmqReconcileStep::AfterGetStatefulSet)(s_prime) {
            if at_rabbitmq_step(key, RabbitmqReconcileStep::AfterGetStatefulSet)(s) {
                assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                assert(s_prime.reconcile_state_of(key).pending_req_msg.is_Some());
                assert(is_get_stateful_set_request(s_prime.pending_req_of(key).content.get_APIRequest_0(), rabbitmq));
            } else {
                assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateRoleBinding)(s));
                assert(s_prime.reconcile_state_of(key).pending_req_msg.is_Some());
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
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        if !s.message_in_flight(msg) {
                            assert(RMQCluster::in_flight_or_pending_req_message(s, s.pending_req_of(key)));
                            assert(RMQCluster::in_flight_or_pending_req_message(s, input.get_Some_0()));
                            assert(is_get_stateful_set_request(s_prime.pending_req_of(key).content.get_APIRequest_0(), rabbitmq));
                            assert(msg.content.is_get_response());
                            assert(msg == RMQCluster::handle_get_request(s.pending_req_of(key), s.kubernetes_api_state).1);
                            assert(msg.src.is_KubernetesAPI()
                            && msg.content.is_get_response());
                            if msg.content.get_get_response().res.is_Ok() {
                                assert(s.resource_key_exists(make_stateful_set_key(key)));
                                assert(s.resource_obj_of(make_stateful_set_key(key)).object_ref() == make_stateful_set_key(key));
                            }
                            assert(sts_get_response_msg(key)(msg));
                        }
                    },
                    Step::KubernetesBusy(input) => {
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        if !s.message_in_flight(msg) {
                            assert(RMQCluster::in_flight_or_pending_req_message(s, s.pending_req_of(key)));
                            assert(RMQCluster::in_flight_or_pending_req_message(s, input.get_Some_0()));
                            assert(msg.src.is_KubernetesAPI());
                            assert(msg.content.is_get_response());
                            assert(msg.content.get_get_response().res.is_Err());
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
                        && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
                ) && (
                    ok_sts_get_response_msg(rabbitmq.object_ref())(msg)
                    ==> msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
                        && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
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
            && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
    };
    let get_rv_leq = |msg: Message, s: RMQCluster| {
        ok_sts_get_response_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
            && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
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
            } else if sts_update_request_msg(rabbitmq.object_ref())(msg) {
                lemma_stateful_set_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s_prime));
            } else if ok_sts_get_response_msg(rabbitmq.object_ref())(msg) {
                let input = step.get_KubernetesAPIStep_0().get_Some_0();
                assert(s.resource_key_exists(input.content.get_get_request().key));
                assert(input.content.get_get_request().key == sts_key);
                assert(msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() == s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0());
                assert(s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter);
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

// if the resource versions do not equal when created, it will never equal each other
spec fn replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            && sts_update_request_msg(rabbitmq.object_ref())(msg)
            && s.resource_key_exists(sts_key)
            && s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == msg.content.get_update_request().obj.metadata.resource_version.get_Some_0()
            ==> replicas_of_stateful_set(s.resource_obj_of(sts_key)) <= replicas_of_stateful_set(msg.content.get_update_request().obj)
    }
}

spec fn helper_3_spec_ok_get_resp(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let sts_key = make_stateful_set_key(key);
        forall |msg|
            #[trigger] s.message_in_flight(msg)
            && ok_sts_get_response_msg(key)(msg)
            && s.resource_key_exists(sts_key)
            && s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0()
            ==> s.resource_obj_of(sts_key) == msg.content.get_get_response().res.get_Ok_0()
    }
}

proof fn lemma_always_helper_3_spec(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(helper_3_spec_ok_get_resp(rabbitmq)))),
{
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(key);
    let inv = helper_3_spec_ok_get_resp(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(rabbitmq)(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    lemma_always_stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(spec, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && ok_sts_get_response_msg(key)(msg) && s_prime.resource_key_exists(sts_key)
        && s_prime.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() implies s_prime.resource_obj_of(sts_key) == msg.content.get_get_response().res.get_Ok_0() by {
            if s.message_in_flight(msg) {
                if !s.resource_key_exists(sts_key) || s.resource_obj_of(sts_key) != s_prime.resource_obj_of(sts_key) {
                    assert(s_prime.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() != msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0())
                }
            } else {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                assert(step.is_KubernetesAPIStep());
                let req = step.get_KubernetesAPIStep_0().get_Some_0();
                assert(msg == RMQCluster::handle_get_request(req, s.kubernetes_api_state).1);
                assert(s.resource_key_exists(req.content.get_get_request().key));
                assert(msg.content.get_get_response().res.get_Ok_0() == s.resource_obj_of(req.content.get_get_request().key));
                assert(req.content.get_get_request().key == msg.content.get_get_response().res.get_Ok_0().object_ref());
                assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
                assert(s_prime.resource_obj_of(sts_key) == msg.content.get_get_response().res.get_Ok_0());
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

proof fn lemma_always_replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)))),
{
    let inv = replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)(s_prime)
        &&& stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(rabbitmq)(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& helper_3_spec_ok_get_resp(rabbitmq)(s)
        &&& response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq)(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    lemma_always_replicas_of_etcd_stateful_set_satisfies_order(spec, rabbitmq);
    always_to_always_later(spec, lift_state(replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)));
    lemma_always_stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(spec, rabbitmq);
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    lemma_always_helper_3_spec(spec, rabbitmq);
    lemma_always_response_at_after_get_stateful_set_step_is_sts_get_response(spec, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()), later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        later(lift_state(replicas_of_etcd_stateful_set_satisfies_order(rabbitmq))),
        lift_state(stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(rabbitmq)),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(helper_3_spec_ok_get_resp(rabbitmq)),
        lift_state(response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        helper_2(rabbitmq, s, s_prime);
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}


proof fn helper_2(rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster)
    requires
        RMQCluster::next()(s, s_prime),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s_prime),
        replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)(s_prime),
        replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)(s),
        stateful_set_in_get_response_and_update_request_have_no_larger_resource_version_than_etcd(rabbitmq)(s),
        RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        helper_3_spec_ok_get_resp(rabbitmq)(s),
        response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq)(s),
    ensures
        replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)(s_prime),
{
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(key);
    assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && sts_update_request_msg(rabbitmq.object_ref())(msg)
    && s_prime.resource_key_exists(sts_key)
    && s_prime.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() implies StatefulSetView::from_dynamic_object(s_prime.resource_obj_of(sts_key)).get_Ok_0().spec.get_Some_0().replicas.get_Some_0()
    <= replicas_of_stateful_set(msg.content.get_update_request().obj) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        if s.message_in_flight(msg) {
            if !s.resource_key_exists(sts_key) || s.resource_obj_of(sts_key) != s_prime.resource_obj_of(sts_key) {
                assert(s_prime.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == s.kubernetes_api_state.resource_version_counter);
                assert(msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter);
                assert(false);
            } else {
                assert(StatefulSetView::from_dynamic_object(s_prime.resource_obj_of(sts_key)).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() <= replicas_of_stateful_set(msg.content.get_update_request().obj));
            }
        } else {
            lemma_stateful_set_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
            StatefulSetView::spec_integrity_is_preserved_by_marshal();
            assert(s_prime.resource_obj_of(sts_key) == s.resource_obj_of(sts_key));
            assert(replicas_of_stateful_set(msg.content.get_update_request().obj) == s.triggering_cr_of(key).spec.replicas);
            assert(s.triggering_cr_of(key) == s_prime.triggering_cr_of(key));
            assert(s_prime.resource_obj_of(sts_key).metadata.owner_references_only_contains(s.triggering_cr_of(key).controller_owner_ref()));
            assert(StatefulSetView::from_dynamic_object(s_prime.resource_obj_of(sts_key)).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() <= replicas_of_stateful_set(msg.content.get_update_request().obj));
        }
    }
}

proof fn lemma_always_replicas_of_etcd_stateful_set_satisfies_order(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)))),
{
    let inv = replicas_of_etcd_stateful_set_satisfies_order(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter()(s)
        &&& replicas_of_stateful_set_update_request_msg_satisfies_order(rabbitmq)(s)
        &&& replicas_of_stateful_set_create_request_msg_satisfies_order(rabbitmq)(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(spec);
    lemma_always_replicas_of_stateful_set_create_request_msg_satisfies_order(spec, rabbitmq);
    lemma_always_replicas_of_stateful_set_update_request_msg_satisfies_order(spec, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter()),
        lift_state(replicas_of_stateful_set_update_request_msg_satisfies_order(rabbitmq)),
        lift_state(replicas_of_stateful_set_create_request_msg_satisfies_order(rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        helper_1(rabbitmq, s, s_prime);
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

proof fn helper_1(rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster)
    requires
        RMQCluster::next()(s, s_prime),
        replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)(s),
        replicas_of_stateful_set_update_request_msg_satisfies_order(rabbitmq)(s),
        replicas_of_stateful_set_create_request_msg_satisfies_order(rabbitmq)(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s_prime),
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

spec fn owner_references_is_valid(obj: DynamicObjectView, s: RMQCluster) -> bool {
    if obj.kind.is_CustomResourceKind() {
        true
    } else {
        let owner_refs = obj.metadata.owner_references.get_Some_0();
        forall |i|
            #![auto] 0 <= i < owner_refs.len()
            ==> owner_refs[i].uid < s.kubernetes_api_state.uid_counter
    }
    
}

spec fn object_in_every_create_or_update_request_msg_only_has_valid_owner_references() -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |msg|
            #[trigger] s.message_in_flight(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_APIRequest()
            ==> (
                msg.content.is_create_request() && msg.content.get_create_request().obj.metadata.owner_references.is_Some()
                ==> owner_references_is_valid(msg.content.get_create_request().obj, s)
            ) && (
                msg.content.is_update_request() && msg.content.get_update_request().obj.metadata.owner_references.is_Some()
                ==> owner_references_is_valid(msg.content.get_update_request().obj, s)
            )
    }
}

proof fn lemma_always_object_in_every_create_or_update_request_msg_only_has_valid_owner_references(spec: TempPred<RMQCluster>)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(object_in_every_create_or_update_request_msg_only_has_valid_owner_references()))),
{
    let inv = object_in_every_create_or_update_request_msg_only_has_valid_owner_references();
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::triggering_cr_has_lower_uid_than_uid_counter()(s)
    };
    RMQCluster::lemma_always_triggering_cr_has_lower_uid_than_uid_counter(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(RMQCluster::triggering_cr_has_lower_uid_than_uid_counter())
    );
    let create_valid = |msg: Message, s: RMQCluster| {
        msg.content.is_create_request() && msg.content.get_create_request().obj.metadata.owner_references.is_Some()
        ==> owner_references_is_valid(msg.content.get_create_request().obj, s)
    };
    let update_valid = |msg: Message, s: RMQCluster| {
        msg.content.is_update_request() && msg.content.get_update_request().obj.metadata.owner_references.is_Some()
        ==> owner_references_is_valid(msg.content.get_update_request().obj, s)
    };
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && msg.dst.is_KubernetesAPI() && msg.content.is_APIRequest()
        implies create_valid(msg, s_prime) && update_valid(msg, s_prime) by {
            assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
            if !s.message_in_flight(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        let cr = s.triggering_cr_of(input.2.get_Some_0());
                        if msg.content.is_create_request() {
                            let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
                            if owner_refs.is_Some() {
                                assert(owner_refs == Some(seq![cr.controller_owner_ref()]));
                            }
                        } else if msg.content.is_update_request() {
                            let owner_refs = msg.content.get_update_request().obj.metadata.owner_references;
                            if owner_refs.is_Some() {
                                assert(owner_refs == Some(seq![cr.controller_owner_ref()]));
                            }
                        }
                    },
                    Step::ClientStep(_) => {
                        if msg.content.is_create_request() {
                            assert(msg.content.get_create_request().obj.kind.is_CustomResourceKind());
                        } else if msg.content.is_update_request() {
                            assert(msg.content.get_update_request().obj.kind.is_CustomResourceKind());
                        }
                    },
                    Step::BuiltinControllersStep(_) => {
                        assert(!msg.content.is_update_request() && !msg.content.is_create_request());
                    },
                    _ => {}
                }
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

spec fn every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter() -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |key|
            #[trigger] s.resource_key_exists(key)
            && s.resource_obj_of(key).metadata.owner_references.is_Some()
            ==> owner_references_is_valid(s.resource_obj_of(key), s)
    }
}

proof fn lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(spec: TempPred<RMQCluster>)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter()))),
{
    let inv = every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter();
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& object_in_every_create_or_update_request_msg_only_has_valid_owner_references()(s)
    };
    lemma_always_object_in_every_create_or_update_request_msg_only_has_valid_owner_references(spec);
    combine_spec_entails_always_n!(spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(object_in_every_create_or_update_request_msg_only_has_valid_owner_references()));
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |key|
        #[trigger] s_prime.resource_key_exists(key) && s_prime.resource_obj_of(key).metadata.owner_references.is_Some()
        implies owner_references_is_valid(s_prime.resource_obj_of(key), s_prime) by {
            assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
            if !s.resource_key_exists(key) || s.resource_obj_of(key).metadata.owner_references != s_prime.resource_obj_of(key).metadata.owner_references {} else {}
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

// show that update msg resource version <= s.resource_obj_of(sts_key) resource version
spec fn replicas_of_stateful_set_update_request_msg_satisfies_order(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            && sts_update_request_msg(rabbitmq.object_ref())(msg)
            ==> msg.content.get_update_request().obj.kind == Kind::StatefulSetKind
                && replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s)
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

// create and update msg should be similar except that update requires another invariant
proof fn lemma_always_replicas_of_stateful_set_create_request_msg_satisfies_order(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(replicas_of_stateful_set_create_request_msg_satisfies_order(rabbitmq)))),
{
    let inv = replicas_of_stateful_set_create_request_msg_satisfies_order(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s)
        &&& triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s)
        &&& triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq)(s)
        &&& object_in_every_create_or_update_request_msg_only_has_valid_owner_references()(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    lemma_always_scheduled_cr_has_no_larger_replicas_than_current_cr(spec, rabbitmq);
    lemma_always_triggering_cr_has_no_larger_replicas_than_scheduled_cr_and_current_cr(spec, rabbitmq);
    lemma_always_object_in_every_create_or_update_request_msg_only_has_valid_owner_references(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq)),
        lift_state(triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)),
        lift_state(triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq)),
        lift_state(object_in_every_create_or_update_request_msg_only_has_valid_owner_references())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && sts_create_request_msg(rabbitmq.object_ref())(msg)
        implies replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s_prime) by {
            let step = choose |step| RMQCluster::next_step(s, s_prime, step);
            let key = rabbitmq.object_ref();
            let sts_key = make_stateful_set_key(key);
            match step {
                Step::KubernetesAPIStep(input) => {
                    assert(s.message_in_flight(msg));
                    assert(s.controller_state == s_prime.controller_state);
                    if s_prime.resource_key_exists(key) {
                        if s.resource_key_exists(key) {
                            assert(replicas_of_rabbitmq(s.resource_obj_of(key)) <= replicas_of_rabbitmq(s_prime.resource_obj_of(key)));
                        } else {
                            assert(s_prime.resource_obj_of(key).metadata.uid.is_Some());
                            assert(s_prime.resource_obj_of(key).metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                            let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
                            if owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1 {
                                assert(owner_refs.get_Some_0()[0].uid != s.kubernetes_api_state.uid_counter);
                                assert(owner_refs.get_Some_0()[0] != RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).get_Ok_0().controller_owner_ref());
                            }
                        }
                    }
                    assert(replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s_prime));
                },
                Step::ControllerStep(input) => {
                    if !s.message_in_flight(msg) {
                        lemma_stateful_set_create_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                        let cr = s.triggering_cr_of(key);
                        StatefulSetView::spec_integrity_is_preserved_by_marshal();
                        assert(replicas_of_stateful_set(msg.content.get_create_request().obj) == cr.spec.replicas);
                    } else {
                        assert(replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s_prime));
                    }
                },
                Step::ScheduleControllerReconcileStep(input) => {
                    assert(s.message_in_flight(msg));
                    assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
                    if input == key {} else {}
                    assert(replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s_prime));
                },
                Step::RestartController() => {
                    assert(s.message_in_flight(msg));
                    assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
                    assert(!s_prime.reconcile_state_contains(key));
                    assert(!s_prime.reconcile_scheduled_for(key));
                    assert(replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s_prime));
                },
                _ => {
                    assert(s.message_in_flight(msg));
                    assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
                    assert(s.controller_state == s_prime.controller_state);
                    assert(replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s_prime));
                }
            }
        } 
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

proof fn lemma_always_replicas_of_stateful_set_update_request_msg_satisfies_order(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(replicas_of_stateful_set_update_request_msg_satisfies_order(rabbitmq)))),
{
    let inv = replicas_of_stateful_set_update_request_msg_satisfies_order(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s)
        &&& triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)(s)
        &&& triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq)(s)
        &&& object_in_every_create_or_update_request_msg_only_has_valid_owner_references()(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    lemma_always_scheduled_cr_has_no_larger_replicas_than_current_cr(spec, rabbitmq);
    lemma_always_triggering_cr_has_no_larger_replicas_than_scheduled_cr_and_current_cr(spec, rabbitmq);
    lemma_always_object_in_every_create_or_update_request_msg_only_has_valid_owner_references(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(scheduled_cr_has_no_larger_replicas_than_current_cr(rabbitmq)),
        lift_state(triggering_cr_has_no_larger_replicas_than_current_cr(rabbitmq)),
        lift_state(triggering_cr_has_no_larger_replicas_than_scheduled_cr(rabbitmq)),
        lift_state(object_in_every_create_or_update_request_msg_only_has_valid_owner_references())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && sts_update_request_msg(rabbitmq.object_ref())(msg)
        implies msg.content.get_update_request().obj.kind == Kind::StatefulSetKind && replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime) by {
            let step = choose |step| RMQCluster::next_step(s, s_prime, step);
            let key = rabbitmq.object_ref();
            let sts_key = make_stateful_set_key(key);
            match step {
                Step::KubernetesAPIStep(input) => {
                    assert(s.message_in_flight(msg));
                    assert(msg.content.get_update_request().obj.kind == Kind::StatefulSetKind);
                    assert(s.controller_state == s_prime.controller_state);
                    if s_prime.resource_key_exists(key) {
                        if s.resource_key_exists(key) {
                            assert(replicas_of_rabbitmq(s.resource_obj_of(key)) <= replicas_of_rabbitmq(s_prime.resource_obj_of(key)));
                        } else {
                            assert(s_prime.resource_obj_of(key).metadata.uid.is_Some());
                            assert(s_prime.resource_obj_of(key).metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                            let owner_refs = msg.content.get_update_request().obj.metadata.owner_references;
                            assert(s.message_in_flight(msg)
                            && msg.dst.is_KubernetesAPI()
                            && msg.content.is_APIRequest());
                            if owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1 {
                                assert(owner_references_is_valid(msg.content.get_update_request().obj, s));
                                assert(!msg.content.get_update_request().obj.kind.is_CustomResourceKind());
                                assert(owner_refs.get_Some_0()[0].uid < s.kubernetes_api_state.uid_counter);
                                assert(owner_refs.get_Some_0()[0] != RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).get_Ok_0().controller_owner_ref());
                            }
                        }
                    }
                    assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
                },
                Step::ControllerStep(input) => {
                    if !s.message_in_flight(msg) {
                        lemma_stateful_set_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                        let cr = s.triggering_cr_of(key);
                        StatefulSetView::spec_integrity_is_preserved_by_marshal();
                        assert(replicas_of_stateful_set(msg.content.get_update_request().obj) == cr.spec.replicas);
                        assert(msg.content.get_update_request().obj.kind == Kind::StatefulSetKind);
                    } else {
                        assert(msg.content.get_update_request().obj.kind == Kind::StatefulSetKind);
                        assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
                    }
                },
                Step::ScheduleControllerReconcileStep(input) => {
                    assert(s.message_in_flight(msg));
                    assert(msg.content.get_update_request().obj.kind == Kind::StatefulSetKind);
                    assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
                    if input == key {} else {}
                    assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
                },
                Step::RestartController() => {
                    assert(s.message_in_flight(msg));
                    assert(msg.content.get_update_request().obj.kind == Kind::StatefulSetKind);
                    assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
                    assert(!s_prime.reconcile_state_contains(key));
                    assert(!s_prime.reconcile_scheduled_for(key));
                    assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
                },
                _ => {
                    assert(s.message_in_flight(msg));
                    assert(msg.content.get_update_request().obj.kind == Kind::StatefulSetKind);
                    assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
                    assert(s.controller_state == s_prime.controller_state);
                    assert(replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime));
                }
            }
        } 
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

}
