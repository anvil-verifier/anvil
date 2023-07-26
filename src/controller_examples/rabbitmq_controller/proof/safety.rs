// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, error::*, resource::*,
};
use crate::kubernetes_cluster::{
    proof::{
        cluster::*,
        cluster_safety::{
            each_key_in_reconcile_is_consistent_with_its_object,
            lemma_always_each_key_in_reconcile_is_consistent_with_its_object,
        },
        controller_runtime::*,
        controller_runtime_eventual_safety,
        controller_runtime_safety::{
            each_resp_matches_at_most_one_pending_req,
            every_in_flight_msg_has_lower_id_than_allocator, every_in_flight_msg_has_unique_id,
            lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state,
        },
        kubernetes_api_safety,
    },
    spec::{
        cluster::*,
        controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::controller,
        kubernetes_api::state_machine::{
            handle_request, object_has_well_formed_spec, transition_by_etcd,
        },
        message::*,
    },
};
use crate::pervasive_ext::{multiset_lemmas, seq_lemmas};
use crate::rabbitmq_controller::{
    common::*,
    proof::common::*,
    spec::{rabbitmqcluster::*, reconciler::*},
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub open spec fn cm_create_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == make_server_config_map_key(key).namespace
        && msg.content.get_create_request().obj.metadata.name.get_Some_0() == make_server_config_map_key(key).name
        && msg.content.get_create_request().obj.kind == make_server_config_map_key(key).kind
}

pub open spec fn cm_create_request_msg_since(key: ObjectRef, rest_id: RestId) -> FnSpec(Message) -> bool {
    |msg: Message|
        cm_create_request_msg(key)(msg)
        && msg.content.get_rest_id() >= rest_id
}

pub open spec fn cm_update_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_update_request()
        && msg.content.get_update_request().key == make_server_config_map_key(key)
}

pub open spec fn cm_update_request_msg_since(key: ObjectRef, rest_id: RestId) -> FnSpec(Message) -> bool {
    |msg: Message|
        cm_update_request_msg(key)(msg)
        && msg.content.get_rest_id() >= rest_id
}

pub open spec fn pending_msg_at_after_create_server_config_map_step_is_create_cm_req(
    key: ObjectRef
) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s)
            ==> {
                &&& pending_k8s_api_req_msg(s, key)
                &&& cm_create_request_msg(key)(s.pending_req_of(key))
            }
    }
}

pub proof fn lemma_always_pending_msg_at_after_create_server_config_map_step_is_create_cm_req(
    spec: TempPred<ClusterState>, key: ObjectRef
)
    requires
        spec.entails(lift_state(init::<RabbitmqClusterView, RabbitmqReconciler>())),
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()))),
    ensures
        spec.entails(
            always(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))
        ),
{
    let invariant = pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key);
    let init = init::<RabbitmqClusterView, RabbitmqReconciler>();
    let stronger_next = |s, s_prime| {
        &&& next::<RabbitmqClusterView, RabbitmqReconciler>()(s, s_prime)
        &&& each_key_in_reconcile_is_consistent_with_its_object()(s)
    };

    lemma_always_each_key_in_reconcile_is_consistent_with_its_object::<RabbitmqClusterView, RabbitmqReconciler>(spec);

    entails_always_and_n!(
        spec,
        lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()),
        lift_state(each_key_in_reconcile_is_consistent_with_its_object())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>())
        .and(lift_state(each_key_in_reconcile_is_consistent_with_its_object()))
    );

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn pending_msg_at_after_update_server_config_map_step_is_update_cm_req(
    key: ObjectRef
) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s)
            ==> {
                &&& pending_k8s_api_req_msg(s, key)
                &&& cm_update_request_msg(key)(s.pending_req_of(key))
            }
    }
}

pub proof fn lemma_always_pending_msg_at_after_update_server_config_map_step_is_update_cm_req(
    spec: TempPred<ClusterState>, key: ObjectRef
)
    requires
        spec.entails(lift_state(init::<RabbitmqClusterView, RabbitmqReconciler>())),
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()))),
    ensures
        spec.entails(
            always(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)))
        ),
{
    let invariant = pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key);
    let init = init::<RabbitmqClusterView, RabbitmqReconciler>();
    let stronger_next = |s, s_prime| {
        &&& next::<RabbitmqClusterView, RabbitmqReconciler>()(s, s_prime)
        &&& each_key_in_reconcile_is_consistent_with_its_object()(s)
    };

    lemma_always_each_key_in_reconcile_is_consistent_with_its_object::<RabbitmqClusterView, RabbitmqReconciler>(spec);

    entails_always_and_n!(
        spec,
        lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()),
        lift_state(each_key_in_reconcile_is_consistent_with_its_object())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>())
        .and(lift_state(each_key_in_reconcile_is_consistent_with_its_object()))
    );

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn at_most_one_create_cm_req_since_rest_id_is_in_flight(
    key: ObjectRef, rest_id: RestId
) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& cm_create_request_msg_since(key, rest_id)(msg)
        } ==> {
            let pending_msg = s.pending_req_of(key);
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s)
            &&& pending_msg.content.get_rest_id() >= rest_id
            &&& msg == pending_msg
            &&& s.network_state.in_flight.count(msg) == 1
        }
    }
}

pub proof fn lemma_always_at_most_one_create_cm_req_since_rest_id_is_in_flight(
    spec: TempPred<ClusterState>, key: ObjectRef, rest_id: RestId
)
    requires
        spec.entails(lift_state(rest_id_counter_is(rest_id))),
        spec.entails(lift_state(every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key))),
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))),
        spec.entails(always(lift_state(each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(at_most_one_create_cm_req_since_rest_id_is_in_flight(key, rest_id)))
        ),
{
    lemma_always_filtered_create_cm_req_len_is_at_most_one(spec, key, rest_id);

    let p = lift_state(at_most_one_create_cm_req_since_rest_id_is_in_flight(key, rest_id));
    let q = lift_state(filtered_create_cm_req_len_is_at_most_one(key, rest_id));

    assert_by(
        p == q, {
            assert forall |ex| p.satisfied_by(ex) implies q.satisfied_by(ex) by {
                multiset_lemmas::filtered_size_is_zero_means_no_such_value(
                    ex.head().network_state.in_flight, cm_create_request_msg_since(key, rest_id)
                );
                multiset_lemmas::filtered_size_is_one_means_only_one_such_value(
                    ex.head().network_state.in_flight, cm_create_request_msg_since(key, rest_id)
                );
            }

            assert forall |ex| q.satisfied_by(ex) implies p.satisfied_by(ex) by {
                multiset_lemmas::filtered_size_is_zero_means_no_such_value(
                    ex.head().network_state.in_flight, cm_create_request_msg_since(key, rest_id)
                );
                multiset_lemmas::filtered_size_is_one_means_only_one_such_value(
                    ex.head().network_state.in_flight, cm_create_request_msg_since(key, rest_id)
                );
            }

            temp_pred_equality(p, q);
        }
    );
}

pub open spec fn at_most_one_update_cm_req_since_rest_id_is_in_flight(
    key: ObjectRef, rest_id: RestId
) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& cm_update_request_msg_since(key, rest_id)(msg)
        } ==> {
            let pending_msg = s.pending_req_of(key);
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s)
            &&& pending_msg.content.get_rest_id() >= rest_id
            &&& msg == pending_msg
            &&& s.network_state.in_flight.count(msg) == 1
        }
    }
}

pub proof fn lemma_always_at_most_one_update_cm_req_since_rest_id_is_in_flight(
    spec: TempPred<ClusterState>, key: ObjectRef, rest_id: RestId
)
    requires
        spec.entails(lift_state(rest_id_counter_is(rest_id))),
        spec.entails(lift_state(every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key))),
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)))),
        spec.entails(always(lift_state(each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(at_most_one_update_cm_req_since_rest_id_is_in_flight(key, rest_id)))
        ),
{
    let init = |s: ClusterState| {
        &&& rest_id_counter_is(rest_id)(s)
        &&& every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)(s)
    };
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<RabbitmqClusterView, RabbitmqReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& busy_disabled()(s)
        &&& pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)(s)
        &&& each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& rest_id_counter_is_no_smaller_than(rest_id)(s)
        &&& every_in_flight_msg_has_unique_id()(s)
    };

    let invariant = at_most_one_update_cm_req_since_rest_id_is_in_flight(key, rest_id);

    entails_and_n!(
        spec,
        lift_state(rest_id_counter_is(rest_id)),
        lift_state(every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key))
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(rest_id_counter_is(rest_id))
        .and(lift_state(every_in_flight_msg_has_lower_id_than_allocator()))
        .and(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)))
    );

    entails_always_and_n!(
        spec,
        lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()),
        lift_state(crash_disabled()),
        lift_state(busy_disabled()),
        lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)),
        lift_state(each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(every_in_flight_msg_has_unique_id())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(busy_disabled()))
        .and(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)))
        .and(lift_state(each_key_in_reconcile_is_consistent_with_its_object()))
        .and(lift_state(rest_id_counter_is_no_smaller_than(rest_id)))
        .and(lift_state(every_in_flight_msg_has_unique_id()))
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        let pending_msg = s_prime.pending_req_of(key);
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && cm_update_request_msg_since(key, rest_id)(msg) implies at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s_prime) && pending_msg.content.get_rest_id() >= rest_id && msg == pending_msg && s_prime.network_state.in_flight.count(msg) == 1 by {
            let step = choose |step| next_step::<RabbitmqClusterView, RabbitmqReconciler>(s, s_prime, step);
            match step {
                Step::KubernetesAPIStep(input) => {
                    assert(s.message_in_flight(msg));
                    assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                    assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s_prime));
                    assert(s_prime.network_state.in_flight.count(msg) == 1);
                }
                Step::ControllerStep(input) => {
                    let cr_key = input.1.get_Some_0();
                    if cr_key != key {
                        if cr_key.name != key.name {
                            seq_lemmas::seq_unequal_preserved_by_add(cr_key.name, key.name, new_strlit("-server-conf")@);
                        }
                        assert(s.message_in_flight(msg));
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s_prime));
                        assert(s_prime.network_state.in_flight.count(msg) == 1);
                    } else {
                        if s.message_in_flight(msg) {
                            assert(input.0.is_Some());
                            assert(resp_msg_matches_req_msg(input.0.get_Some_0(), s.pending_req_of(key)));
                            assert(false);
                        } else {
                            assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s_prime));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    init_invariant(spec, init, stronger_next, invariant);
}


pub open spec fn every_update_cm_req_since_rest_id_does_the_same(
    rabbitmq: RabbitmqClusterView, rest_id: RestId
) -> StatePred<ClusterState>
    recommends
        rabbitmq.well_formed(),
{
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& cm_update_request_msg_since(rabbitmq.object_ref(), rest_id)(msg)
        } ==> msg.content.get_update_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ()))
    }
}

pub proof fn lemma_always_every_update_cm_req_since_rest_id_does_the_same(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rest_id: RestId
)
    requires
        spec.entails(lift_state(rest_id_counter_is(rest_id))),
        spec.entails(lift_state(every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()))),
        spec.entails(always(lift_state(each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(controller_runtime_eventual_safety::the_object_in_reconcile_has_spec_as(rabbitmq)))),
    ensures
        spec.entails(always(lift_state(every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id)))),
{
    let init = |s: ClusterState| {
        &&& rest_id_counter_is(rest_id)(s)
        &&& every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<RabbitmqClusterView, RabbitmqReconciler>()(s, s_prime)
        &&& each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& rest_id_counter_is_no_smaller_than(rest_id)(s)
        &&& controller_runtime_eventual_safety::the_object_in_reconcile_has_spec_as(rabbitmq)(s)
    };
    let invariant = every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id);

    entails_and_n!(
        spec,
        lift_state(rest_id_counter_is(rest_id)),
        lift_state(every_in_flight_msg_has_lower_id_than_allocator())
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(rest_id_counter_is(rest_id))
        .and(lift_state(every_in_flight_msg_has_lower_id_than_allocator()))
    );

    entails_always_and_n!(
        spec,
        lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()),
        lift_state(each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(controller_runtime_eventual_safety::the_object_in_reconcile_has_spec_as(rabbitmq))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>())
        .and(lift_state(each_key_in_reconcile_is_consistent_with_its_object()))
        .and(lift_state(rest_id_counter_is_no_smaller_than(rest_id)))
        .and(lift_state(controller_runtime_eventual_safety::the_object_in_reconcile_has_spec_as(rabbitmq)))
    );

    assert forall |s, s_prime: ClusterState| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |msg: Message|
            #[trigger] s_prime.network_state.in_flight.contains(msg)
            && cm_update_request_msg_since(rabbitmq.object_ref(), rest_id)(msg)
        implies msg.content.get_update_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ())) by {
            if !s.message_in_flight(msg) {
                let step = choose |step| next_step::<RabbitmqClusterView, RabbitmqReconciler>(s, s_prime, step);
                assert(step.is_ControllerStep());
                let other_rmq = s.reconcile_state_of(step.get_ControllerStep_0().1.get_Some_0()).triggering_cr;
                seq_lemmas::seq_equal_preserved_by_add(
                    other_rmq.metadata.name.get_Some_0(),
                    rabbitmq.metadata.name.get_Some_0(),
                    new_strlit("-server-conf")@
                );
                assert(other_rmq.object_ref() == rabbitmq.object_ref());
                assert(other_rmq == s.reconcile_state_of(other_rmq.object_ref()).triggering_cr);
                assert(rabbitmq.spec() == other_rmq.spec());
            }
        }
    }

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn cm_delete_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_delete_request()
        && msg.content.get_delete_request().key == make_server_config_map_key(key)
}

pub open spec fn cm_delete_request_msg_since(key: ObjectRef, rest_id: RestId) -> FnSpec(Message) -> bool {
    |msg: Message|
        cm_delete_request_msg(key)(msg)
        && msg.content.get_rest_id() >= rest_id
}

pub open spec fn no_delete_cm_req_since_rest_id_is_in_flight(
    key: ObjectRef, rest_id: RestId
) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        forall |msg: Message| !{
            &&& #[trigger] s.message_in_flight(msg)
            &&& cm_delete_request_msg_since(key, rest_id)(msg)
        }
    }
}

pub proof fn lemma_always_no_delete_cm_req_since_rest_id_is_in_flight(
    spec: TempPred<ClusterState>, key: ObjectRef, rest_id: RestId
)
    requires
        spec.entails(lift_state(rest_id_counter_is(rest_id))),
        spec.entails(lift_state(every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(no_delete_cm_req_since_rest_id_is_in_flight(key, rest_id)))
        ),
{
    let init = |s: ClusterState| {
        &&& rest_id_counter_is(rest_id)(s)
        &&& every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    let next = next::<RabbitmqClusterView, RabbitmqReconciler>();
    let invariant = no_delete_cm_req_since_rest_id_is_in_flight(key, rest_id);

    entails_and_n!(
        spec,
        lift_state(rest_id_counter_is(rest_id)),
        lift_state(every_in_flight_msg_has_lower_id_than_allocator())
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(rest_id_counter_is(rest_id))
        .and(lift_state(every_in_flight_msg_has_lower_id_than_allocator()))
    );

    assert forall |s, s_prime: ClusterState| invariant(s) && #[trigger] next(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |msg: Message|
        !(#[trigger] s_prime.message_in_flight(msg) && cm_delete_request_msg_since(key, rest_id)(msg)) by {
            if s.message_in_flight(msg) {} else {}
        }
    }

    init_invariant(spec, init, next, invariant);
}

pub open spec fn filtered_create_cm_req_len_is_at_most_one(
    key: ObjectRef, rest_id: RestId
) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        s.network_state.in_flight.filter(cm_create_request_msg_since(key, rest_id)).len() > 0
        ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s)
            &&& s.pending_req_of(key).content.get_rest_id() >= rest_id
            &&& s.message_in_flight(s.pending_req_of(key))
            &&& cm_create_request_msg_since(key, rest_id)(s.pending_req_of(key))
            &&& s.network_state.in_flight.filter(cm_create_request_msg_since(key, rest_id)).len() == 1
        }
    }
}

proof fn lemma_always_filtered_create_cm_req_len_is_at_most_one(
    spec: TempPred<ClusterState>, key: ObjectRef, rest_id: RestId
)
    requires
        spec.entails(lift_state(rest_id_counter_is(rest_id))),
        spec.entails(lift_state(every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key))),
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))),
        spec.entails(always(lift_state(each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(filtered_create_cm_req_len_is_at_most_one(key, rest_id)))
        ),
{
    let init = |s: ClusterState| {
        &&& rest_id_counter_is(rest_id)(s)
        &&& every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)(s)
    };
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<RabbitmqClusterView, RabbitmqReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& busy_disabled()(s)
        &&& pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)(s)
        &&& each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& rest_id_counter_is_no_smaller_than(rest_id)(s)
        &&& every_in_flight_msg_has_unique_id()(s)
    };
    let invariant = filtered_create_cm_req_len_is_at_most_one(key, rest_id);

    entails_and_n!(
        spec,
        lift_state(rest_id_counter_is(rest_id)),
        lift_state(every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key))
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(rest_id_counter_is(rest_id))
        .and(lift_state(every_in_flight_msg_has_lower_id_than_allocator()))
        .and(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))
    );

    entails_always_and_n!(
        spec,
        lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()),
        lift_state(crash_disabled()),
        lift_state(busy_disabled()),
        lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)),
        lift_state(each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(every_in_flight_msg_has_unique_id())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(busy_disabled()))
        .and(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))
        .and(lift_state(each_key_in_reconcile_is_consistent_with_its_object()))
        .and(lift_state(rest_id_counter_is_no_smaller_than(rest_id)))
        .and(lift_state(every_in_flight_msg_has_unique_id()))
    );

    assert forall |s: ClusterState| #[trigger] init(s) implies invariant(s) by {
        let cm_create_req_multiset = s.network_state.in_flight.filter(cm_create_request_msg_since(key, rest_id));

        assert forall |msg| cm_create_req_multiset.count(msg) == 0 by {
            assert(!(s.message_in_flight(msg) && cm_create_request_msg_since(key, rest_id)(msg)));
        }
        multiset_lemmas::len_is_zero_means_count_for_each_value_is_zero(cm_create_req_multiset);
    }

    assert forall |s, s_prime: ClusterState| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        let cm_create_req_multiset = s.network_state.in_flight.filter(cm_create_request_msg_since(key, rest_id));
        let cm_create_req_multiset_prime = s_prime.network_state.in_flight.filter(cm_create_request_msg_since(key, rest_id));
        let step = choose |step| next_step::<RabbitmqClusterView, RabbitmqReconciler>(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if !at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s) {
                    // If not at AfterUpdateServerConfigMap step,
                    // due to inductive hypothesis, the set of messages remains unchanged (len() = 0)
                    // between s and s_prime.
                    assert(cm_create_req_multiset =~= cm_create_req_multiset_prime);
                } else {
                    // If at AfterUpdateServerConfigMap step,
                    // we need to split the case.
                    let chosen_msg = input.get_Some_0();
                    if cm_create_request_msg_since(key, rest_id)(chosen_msg) {
                        // If the chosen message to handle is the one that creates ServerConfigMap,
                        // then the message set shrinks by one.
                        assert(cm_create_req_multiset.remove(chosen_msg) =~= cm_create_req_multiset_prime);
                    } else {
                        // Otherwise the set remains unchanged.
                        assert(cm_create_req_multiset =~= cm_create_req_multiset_prime);
                    }
                }
            },
            Step::ControllerStep(input) => {
                if cm_create_req_multiset_prime.len() > 0 {
                    let chosen_key = input.1.get_Some_0();
                    if chosen_key == key {
                        // If the state machine chooses the reconciler for our key to take the next transition...
                        if at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s_prime) {
                            assert(cm_create_req_multiset.len() == 0);
                            assert(cm_create_req_multiset.insert(s_prime.pending_req_of(key)) =~= cm_create_req_multiset_prime);
                        } else if at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreatePluginsConfigMap)(s_prime) {
                            assert_by(
                                new_strlit("-server-conf")@ != new_strlit("-plugins-conf")@,
                                {
                                    reveal_strlit("-server-conf");
                                    reveal_strlit("-plugins-conf");
                                    assert(new_strlit("-server-conf")@[1] != new_strlit("-plugins-conf")@[1]);
                                }
                            );
                            seq_lemmas::seq_equal_preserved_by_add_prefix(key.name, new_strlit("-server-conf")@, new_strlit("-plugins-conf")@);
                            assert(cm_create_req_multiset =~= cm_create_req_multiset_prime);
                        } else {
                            assert(cm_create_req_multiset =~= cm_create_req_multiset_prime);
                        }
                    } else {
                        if chosen_key.name != key.name {
                            seq_lemmas::seq_unequal_preserved_by_add(chosen_key.name, key.name, new_strlit("-server-conf")@);
                            assert_by(
                                chosen_key.name + new_strlit("-plugins-conf")@ != key.name + new_strlit("-server-conf")@,
                                {
                                    let str1 = chosen_key.name + new_strlit("-plugins-conf")@;
                                    let str2 = key.name + new_strlit("-server-conf")@;
                                    reveal_strlit("-server-conf");
                                    reveal_strlit("-plugins-conf");
                                    if str1.len() == str2.len() {
                                        assert(str1[str1.len() - 6] == 's');
                                        assert(str2[str1.len() - 6] == 'r');
                                    }
                                }
                            );
                        }
                        assert(cm_create_req_multiset =~= cm_create_req_multiset_prime);
                    }
                }
            },
            Step::ClientStep(input) => {
                assert(cm_create_req_multiset =~= cm_create_req_multiset_prime);
            },
            _ => {
            }
        }
    }

    init_invariant(spec, init, stronger_next, invariant);
}

}
