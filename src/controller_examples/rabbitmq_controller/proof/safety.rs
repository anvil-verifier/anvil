// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::EmptyAPI;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, error::*, resource::*,
};
use crate::kubernetes_cluster::{
    spec::{
        cluster::*,
        controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
        controller::state_machine::*,
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
                &&& ClusterProof::pending_k8s_api_req_msg(s, key)
                &&& cm_create_request_msg(key)(s.pending_req_of(key))
            }
    }
}

pub proof fn lemma_always_pending_msg_at_after_create_server_config_map_step_is_create_cm_req(
    spec: TempPred<ClusterState>, key: ObjectRef
)
    requires
        spec.entails(lift_state(ClusterProof::init())),
        spec.entails(always(lift_action(ClusterProof::next()))),
    ensures
        spec.entails(
            always(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))
        ),
{
    let invariant = pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key);
    let init = ClusterProof::init();
    let stronger_next = |s, s_prime| {
        &&& ClusterProof::next()(s, s_prime)
        &&& ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()(s)
    };

    ClusterProof::lemma_always_each_key_in_reconcile_is_consistent_with_its_object(spec);

    entails_always_and_n!(
        spec,
        lift_action(ClusterProof::next()),
        lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ClusterProof::next())
        .and(lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()))
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
                &&& ClusterProof::pending_k8s_api_req_msg(s, key)
                &&& cm_update_request_msg(key)(s.pending_req_of(key))
            }
    }
}

pub proof fn lemma_always_pending_msg_at_after_update_server_config_map_step_is_update_cm_req(
    spec: TempPred<ClusterState>, key: ObjectRef
)
    requires
        spec.entails(lift_state(ClusterProof::init())),
        spec.entails(always(lift_action(ClusterProof::next()))),
    ensures
        spec.entails(
            always(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)))
        ),
{
    let invariant = pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key);
    let init = ClusterProof::init();
    let stronger_next = |s, s_prime| {
        &&& ClusterProof::next()(s, s_prime)
        &&& ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()(s)
    };

    ClusterProof::lemma_always_each_key_in_reconcile_is_consistent_with_its_object(spec);

    entails_always_and_n!(
        spec,
        lift_action(ClusterProof::next()),
        lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ClusterProof::next())
        .and(lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()))
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
        spec.entails(lift_state(ClusterProof::rest_id_counter_is(rest_id))),
        spec.entails(lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key))),
        spec.entails(always(lift_action(ClusterProof::next()))),
        spec.entails(always(lift_state(ClusterProof::crash_disabled()))),
        spec.entails(always(lift_state(ClusterProof::busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))),
        spec.entails(always(lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(ClusterProof::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(at_most_one_create_cm_req_since_rest_id_is_in_flight(key, rest_id)))
        ),
{
    let init = |s: ClusterState| {
        &&& ClusterProof::rest_id_counter_is(rest_id)(s)
        &&& ClusterProof::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)(s)
    };
    let stronger_next = |s, s_prime: ClusterState| {
        &&& ClusterProof::next()(s, s_prime)
        &&& ClusterProof::crash_disabled()(s)
        &&& ClusterProof::busy_disabled()(s)
        &&& pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)(s)
        &&& ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)(s)
        &&& ClusterProof::every_in_flight_msg_has_unique_id()(s)
    };
    let invariant = at_most_one_create_cm_req_since_rest_id_is_in_flight(key, rest_id);

    entails_and_n!(
        spec,
        lift_state(ClusterProof::rest_id_counter_is(rest_id)),
        lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key))
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(ClusterProof::rest_id_counter_is(rest_id))
        .and(lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator()))
        .and(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))
    );

    entails_always_and_n!(
        spec,
        lift_action(ClusterProof::next()),
        lift_state(ClusterProof::crash_disabled()),
        lift_state(ClusterProof::busy_disabled()),
        lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)),
        lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(ClusterProof::every_in_flight_msg_has_unique_id())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ClusterProof::next())
        .and(lift_state(ClusterProof::crash_disabled()))
        .and(lift_state(ClusterProof::busy_disabled()))
        .and(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))
        .and(lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()))
        .and(lift_state(ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)))
        .and(lift_state(ClusterProof::every_in_flight_msg_has_unique_id()))
    );
    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        let pending_msg = s_prime.pending_req_of(key);
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && cm_create_request_msg_since(key, rest_id)(msg) implies at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s_prime) && pending_msg.content.get_rest_id() >= rest_id && msg == pending_msg && s_prime.network_state.in_flight.count(msg) == 1 by {
            let step = choose |step| ClusterProof::next_step(s, s_prime, step);
            match step {
                Step::KubernetesAPIStep(input) => {
                    assert(s.message_in_flight(msg));
                    assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                    assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s_prime));
                    assert(s_prime.network_state.in_flight.count(msg) == 1);
                },
                Step::ControllerStep(input) => {
                    let cr_key = input.2.get_Some_0();
                    if cr_key != key {
                        if cr_key.name != key.name {
                            seq_lemmas::seq_unequal_preserved_by_add(cr_key.name, key.name, new_strlit("-server-conf")@);
                            assert_by(
                                cr_key.name + new_strlit("-plugins-conf")@ != key.name + new_strlit("-server-conf")@,
                                {
                                    let str1 = cr_key.name + new_strlit("-plugins-conf")@;
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
                        assert(s.message_in_flight(msg));
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s_prime));
                        assert(s_prime.network_state.in_flight.count(msg) == 1);
                    } else {
                        assert_by(
                            new_strlit("-server-conf")@ != new_strlit("-plugins-conf")@,
                            {
                                reveal_strlit("-server-conf");
                                reveal_strlit("-plugins-conf");
                                assert(new_strlit("-server-conf")@[1] != new_strlit("-plugins-conf")@[1]);
                            }
                        );
                        seq_lemmas::seq_equal_preserved_by_add_prefix(key.name, new_strlit("-server-conf")@, new_strlit("-plugins-conf")@);
                        if s.message_in_flight(msg) {
                            assert(input.0.is_Some());
                            assert(resp_msg_matches_req_msg(input.0.get_Some_0(), s.pending_req_of(key)));
                            assert(false);
                        } else {
                            assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s_prime));
                        }
                    }
                },
                Step::ClientStep(input) => {
                    assert(s.message_in_flight(msg));
                    assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                    assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s_prime));
                    assert(s_prime.network_state.in_flight.count(msg) == 1);
                },
                _ => {}
            }
        }
    }

    init_invariant(spec, init, stronger_next, invariant);
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
        spec.entails(lift_state(ClusterProof::rest_id_counter_is(rest_id))),
        spec.entails(lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key))),
        spec.entails(always(lift_action(ClusterProof::next()))),
        spec.entails(always(lift_state(ClusterProof::crash_disabled()))),
        spec.entails(always(lift_state(ClusterProof::busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)))),
        spec.entails(always(lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(ClusterProof::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(at_most_one_update_cm_req_since_rest_id_is_in_flight(key, rest_id)))
        ),
{
    let init = |s: ClusterState| {
        &&& ClusterProof::rest_id_counter_is(rest_id)(s)
        &&& ClusterProof::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)(s)
    };
    let stronger_next = |s, s_prime: ClusterState| {
        &&& ClusterProof::next()(s, s_prime)
        &&& ClusterProof::crash_disabled()(s)
        &&& ClusterProof::busy_disabled()(s)
        &&& pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)(s)
        &&& ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)(s)
        &&& ClusterProof::every_in_flight_msg_has_unique_id()(s)
    };

    let invariant = at_most_one_update_cm_req_since_rest_id_is_in_flight(key, rest_id);

    entails_and_n!(
        spec,
        lift_state(ClusterProof::rest_id_counter_is(rest_id)),
        lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key))
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(ClusterProof::rest_id_counter_is(rest_id))
        .and(lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator()))
        .and(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)))
    );

    entails_always_and_n!(
        spec,
        lift_action(ClusterProof::next()),
        lift_state(ClusterProof::crash_disabled()),
        lift_state(ClusterProof::busy_disabled()),
        lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)),
        lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(ClusterProof::every_in_flight_msg_has_unique_id())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ClusterProof::next())
        .and(lift_state(ClusterProof::crash_disabled()))
        .and(lift_state(ClusterProof::busy_disabled()))
        .and(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)))
        .and(lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()))
        .and(lift_state(ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)))
        .and(lift_state(ClusterProof::every_in_flight_msg_has_unique_id()))
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        let pending_msg = s_prime.pending_req_of(key);
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && cm_update_request_msg_since(key, rest_id)(msg) implies at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s_prime) && pending_msg.content.get_rest_id() >= rest_id && msg == pending_msg && s_prime.network_state.in_flight.count(msg) == 1 by {
            let step = choose |step| ClusterProof::next_step(s, s_prime, step);
            match step {
                Step::KubernetesAPIStep(input) => {
                    assert(s.message_in_flight(msg));
                    assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                    assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s_prime));
                    assert(s_prime.network_state.in_flight.count(msg) == 1);
                },
                Step::ControllerStep(input) => {
                    let cr_key = input.2.get_Some_0();
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
                },
                Step::ClientStep(input) => {
                    assert(s.message_in_flight(msg));
                    assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                    assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s_prime));
                    assert(s_prime.network_state.in_flight.count(msg) == 1);
                },
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
        spec.entails(lift_state(ClusterProof::rest_id_counter_is(rest_id))),
        spec.entails(lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(always(lift_action(ClusterProof::next()))),
        spec.entails(always(lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(ClusterProof::the_object_in_reconcile_has_spec_as(rabbitmq)))),
    ensures
        spec.entails(always(lift_state(every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id)))),
{
    let init = |s: ClusterState| {
        &&& ClusterProof::rest_id_counter_is(rest_id)(s)
        &&& ClusterProof::every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    let stronger_next = |s, s_prime: ClusterState| {
        &&& ClusterProof::next()(s, s_prime)
        &&& ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)(s)
        &&& ClusterProof::the_object_in_reconcile_has_spec_as(rabbitmq)(s)
    };
    let invariant = every_update_cm_req_since_rest_id_does_the_same(rabbitmq, rest_id);

    entails_and_n!(
        spec,
        lift_state(ClusterProof::rest_id_counter_is(rest_id)),
        lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator())
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(ClusterProof::rest_id_counter_is(rest_id))
        .and(lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator()))
    );

    entails_always_and_n!(
        spec,
        lift_action(ClusterProof::next()),
        lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(ClusterProof::the_object_in_reconcile_has_spec_as(rabbitmq))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ClusterProof::next())
        .and(lift_state(ClusterProof::each_key_in_reconcile_is_consistent_with_its_object()))
        .and(lift_state(ClusterProof::rest_id_counter_is_no_smaller_than(rest_id)))
        .and(lift_state(ClusterProof::the_object_in_reconcile_has_spec_as(rabbitmq)))
    );

    assert forall |s, s_prime: ClusterState| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |msg: Message|
            #[trigger] s_prime.network_state.in_flight.contains(msg)
            && cm_update_request_msg_since(rabbitmq.object_ref(), rest_id)(msg)
        implies msg.content.get_update_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ())) by {
            if !s.message_in_flight(msg) {
                let step = choose |step| ClusterProof::next_step(s, s_prime, step);
                assert(step.is_ControllerStep());
                let other_rmq = s.reconcile_state_of(step.get_ControllerStep_0().2.get_Some_0()).triggering_cr;
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
        spec.entails(lift_state(ClusterProof::rest_id_counter_is(rest_id))),
        spec.entails(lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(always(lift_action(ClusterProof::next()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(no_delete_cm_req_since_rest_id_is_in_flight(key, rest_id)))
        ),
{
    let init = |s: ClusterState| {
        &&& ClusterProof::rest_id_counter_is(rest_id)(s)
        &&& ClusterProof::every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    let next = ClusterProof::next();
    let invariant = no_delete_cm_req_since_rest_id_is_in_flight(key, rest_id);

    entails_and_n!(
        spec,
        lift_state(ClusterProof::rest_id_counter_is(rest_id)),
        lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator())
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(ClusterProof::rest_id_counter_is(rest_id))
        .and(lift_state(ClusterProof::every_in_flight_msg_has_lower_id_than_allocator()))
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

}
