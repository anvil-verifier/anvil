// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::EmptyAPI;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, error::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    message::*,
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

pub open spec fn cm_update_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_update_request()
        && msg.content.get_update_request().key == make_server_config_map_key(key)
}

pub open spec fn pending_msg_at_after_create_server_config_map_step_is_create_cm_req(
    key: ObjectRef
) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s)
            ==> {
                &&& RMQCluster::pending_k8s_api_req_msg(s, key)
                &&& cm_create_request_msg(key)(s.pending_req_of(key))
            }
    }
}

pub proof fn lemma_always_pending_msg_at_after_create_server_config_map_step_is_create_cm_req(
    spec: TempPred<RMQCluster>, key: ObjectRef
)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(
            always(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))
        ),
{
    let invariant = pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key);
    let init = RMQCluster::init();
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
    };

    RMQCluster::lemma_always_each_key_in_reconcile_is_consistent_with_its_object(spec);

    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))
    );

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn pending_msg_at_after_update_server_config_map_step_is_update_cm_req(
    key: ObjectRef
) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s)
            ==> {
                &&& RMQCluster::pending_k8s_api_req_msg(s, key)
                &&& cm_update_request_msg(key)(s.pending_req_of(key))
            }
    }
}

pub proof fn lemma_always_pending_msg_at_after_update_server_config_map_step_is_update_cm_req(
    spec: TempPred<RMQCluster>, key: ObjectRef
)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(
            always(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)))
        ),
{
    let invariant = pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key);
    let init = RMQCluster::init();
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
    };

    RMQCluster::lemma_always_each_key_in_reconcile_is_consistent_with_its_object(spec);

    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))
    );

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn at_most_one_create_cm_req_is_in_flight(key: ObjectRef) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& cm_create_request_msg(key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s)
            &&& msg == s.pending_req_of(key)
            &&& s.network_state.in_flight.count(msg) == 1
        }
    }
}

pub proof fn lemma_true_leads_to_always_at_most_one_create_cm_req_is_in_flight(spec: TempPred<RMQCluster>, key: ObjectRef)
    requires
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(at_most_one_create_cm_req_is_in_flight(key))))
        ),
{
    let requirements = |msg: Message, s: RMQCluster| {
        cm_create_request_msg(key)(msg)
        ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s)
            &&& msg == s.pending_req_of(key)
            &&& s.network_state.in_flight.count(msg) == 1
        }
    };
    let stronger_next = |s: RMQCluster, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.message_in_flight(msg) || requirements(msg, s)) && #[trigger] s_prime.message_in_flight(msg)
        implies requirements(msg, s_prime) by {
            if cm_create_request_msg(key)(msg) {
                let pending_req = s_prime.pending_req_of(key);
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                match step {
                    Step::KubernetesAPIStep(input) => {
                        assert(s.controller_state == s_prime.controller_state);
                        assert(s.message_in_flight(msg));
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateServerConfigMap)(s_prime));
                        assert(s.network_state.in_flight.count(msg) == 1);
                        assert(msg.dst.is_KubernetesAPI());
                        assert(s_prime.network_state.in_flight.count(msg) == 1);
                    },
                    Step::BuiltinControllersStep(input) => {
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
    }
    invariant_action_n!(
        spec, stronger_next, RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::crash_disabled()), lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(pending_msg_at_after_create_server_config_map_step_is_create_cm_req(key))
    );

    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(lift_state(at_most_one_create_cm_req_is_in_flight(key)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn at_most_one_update_cm_req_is_in_flight(key: ObjectRef) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& cm_update_request_msg(key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s)
            &&& msg == s.pending_req_of(key)
            &&& s.network_state.in_flight.count(msg) == 1
        }
    }
}

pub proof fn lemma_true_leads_to_always_at_most_one_update_cm_req_is_in_flight(spec: TempPred<RMQCluster>, key: ObjectRef)
    requires
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)))),
        spec.entails(always(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(at_most_one_update_cm_req_is_in_flight(key))))
        ),
{
    let requirements = |msg: Message, s: RMQCluster| {
        cm_update_request_msg(key)(msg)
        ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s)
            &&& msg == s.pending_req_of(key)
            &&& s.network_state.in_flight.count(msg) == 1
        }
    };
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)(s)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        let pending_msg = s_prime.pending_req_of(key);
        assert forall |msg| (!s.message_in_flight(msg) || requirements(msg, s)) && #[trigger] s_prime.message_in_flight(msg) implies requirements(msg, s_prime) by {
            if cm_update_request_msg(key)(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                match step {
                    Step::KubernetesAPIStep(input) => {
                        assert(s.message_in_flight(msg));
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateServerConfigMap)(s_prime));
                        assert(s_prime.network_state.in_flight.count(msg) == 1);
                    },
                    Step::BuiltinControllersStep(input) => {
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
    }

    invariant_action_n!(
        spec, stronger_next, RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(pending_msg_at_after_update_server_config_map_step_is_update_cm_req(key)),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id())
    );
    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(at_most_one_update_cm_req_is_in_flight(key)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}


pub open spec fn every_update_cm_req_does_the_same(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        forall |msg: Message| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& cm_update_request_msg(rabbitmq.object_ref())(msg)
        } ==> msg.content.get_update_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ()))
        && && msg.content.get_update_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    }
}

pub open spec fn stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.resource_key_exists(make_stateful_set_key(rabbitmq.object_ref()))
        ==> s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref())).metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
    }
}

pub open spec fn server_config_map_has_owner_reference_pointing_to_current_cr(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        ==> s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())).metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
    }
}

pub open spec fn server_config_map_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.resource_key_exists(make_server_config_map_key(rabbitmq.object_ref()))
        ==>
            s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())).metadata.deletion_timestamp.is_None()
            && s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())).metadata.finalizers.is_None()
            && exists |uid: nat| #![auto]
            s.resource_obj_of(make_server_config_map_key(rabbitmq.object_ref())).metadata.owner_references == Some(seq![OwnerReferenceView {
                block_owner_deletion: None,
                controller: Some(true),
                kind: RabbitmqClusterView::kind(),
                name: rabbitmq.metadata.name.get_Some_0(),
                uid: uid,
            }])
    }
}

#[verifier(external_body)]
pub proof fn lemma_always_server_config_map_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(server_config_map_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)))),
{}

pub open spec fn stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.resource_key_exists(make_stateful_set_key(rabbitmq.object_ref()))
        ==>
            s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref())).metadata.deletion_timestamp.is_None()
            && s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref())).metadata.finalizers.is_None()
            && exists |uid: nat| #![auto]
            s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref())).metadata.owner_references == Some(seq![OwnerReferenceView {
                block_owner_deletion: None,
                controller: Some(true),
                kind: RabbitmqClusterView::kind(),
                name: rabbitmq.metadata.name.get_Some_0(),
                uid: uid,
            }])
    }
}

#[verifier(external_body)]
pub proof fn lemma_always_stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)))),
{
    let invariant = stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq);
    assert forall |s, s_prime: RMQCluster| invariant(s) && #[trigger] RMQCluster::next()(s, s_prime) implies invariant(s_prime) by {

    }
    init_invariant(spec, RMQCluster::init(), RMQCluster::next(), invariant);
}

pub proof fn lemma_true_leads_to_always_every_update_cm_req_does_the_same(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)))),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(every_update_cm_req_does_the_same(rabbitmq))))
        ),
{
    let requirements = |msg: Message, s: RMQCluster| {
        cm_update_request_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_update_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ()))
        && msg.content.get_update_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    };
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.message_in_flight(msg) || requirements(msg, s)) && #[trigger] s_prime.message_in_flight(msg)
        && msg.dst.is_KubernetesAPI() && msg.content.is_APIRequest() implies requirements(msg, s_prime) by {
            if !s.message_in_flight(msg) && cm_update_request_msg(rabbitmq.object_ref())(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
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
    invariant_action_n!(
        spec, stronger_next, RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))
    );
    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(every_update_cm_req_does_the_same(rabbitmq)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn cm_delete_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_delete_request()
        && msg.content.get_delete_request().key == make_server_config_map_key(key)
}

pub open spec fn no_delete_cm_req_is_in_flight(key: ObjectRef) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        forall |msg: Message| !{
            &&& #[trigger] s.message_in_flight(msg)
            &&& cm_delete_request_msg(key)(msg)
        }
    }
}

pub proof fn lemma_true_leads_to_always_no_delete_cm_req_is_in_flight(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(server_config_map_has_owner_reference_pointing_to_current_cr(rabbitmq))))
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(no_delete_cm_req_is_in_flight(rabbitmq.object_ref()))))
        ),
{
    let key = rabbitmq.object_ref();
    let requirements = |msg: Message, s: RMQCluster| !cm_delete_request_msg(key)(msg);

    let stronger_next = |s: RMQCluster, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::desired_state_is(rabbitmq)(s)
        &&& server_config_map_has_owner_reference_pointing_to_current_cr(rabbitmq)(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
    };
    assert forall |s: RMQCluster, s_prime: RMQCluster| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.message_in_flight(msg) || requirements(msg, s)) && #[trigger] s_prime.message_in_flight(msg)
        implies requirements(msg, s_prime) by {
            if s.resource_key_exists(make_server_config_map_key(key)) {
                let owner_refs = s.resource_obj_of(make_server_config_map_key(key)).metadata.owner_references;
                assert(owner_refs == Some(seq![rabbitmq.controller_owner_ref()]));
                assert(owner_reference_to_object_reference(owner_refs.get_Some_0()[0], key.namespace) == key);
            }
        }
    }
    invariant_action_n!(
        spec, stronger_next, RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(server_config_map_has_owner_reference_pointing_to_current_cr(rabbitmq)),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed())
    );

    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(no_delete_cm_req_is_in_flight(key)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn sts_create_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == make_stateful_set_key(key).namespace
        && msg.content.get_create_request().obj.metadata.name.get_Some_0() == make_stateful_set_key(key).name
        && msg.content.get_create_request().obj.kind == make_stateful_set_key(key).kind
}

pub open spec fn sts_update_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_update_request()
        && msg.content.get_update_request().key == make_stateful_set_key(key)
}

pub open spec fn every_update_sts_req_does_the_same(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        forall |msg: Message| {
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
        spec.entails(always(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)))),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(every_update_sts_req_does_the_same(rabbitmq))))
        ),
{
    let requirements = |msg: Message, s: RMQCluster| {
        sts_update_request_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_update_request().obj.spec == StatefulSetView::marshal_spec(make_stateful_set(rabbitmq).spec)
        && msg.content.get_update_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    };
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.message_in_flight(msg) || requirements(msg, s)) && #[trigger] s_prime.message_in_flight(msg)
        && msg.dst.is_KubernetesAPI() && msg.content.is_APIRequest() implies requirements(msg, s_prime) by {
            if !s.message_in_flight(msg) && sts_update_request_msg(rabbitmq.object_ref())(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                assert(step.is_ControllerStep());
                let other_rmq = s.reconcile_state_of(step.get_ControllerStep_0().2.get_Some_0()).triggering_cr;
                seq_lemmas::seq_equal_preserved_by_add(
                    other_rmq.metadata.name.get_Some_0(),
                    rabbitmq.metadata.name.get_Some_0(),
                    new_strlit("-server")@
                );
                assert(other_rmq.object_ref() == rabbitmq.object_ref());
                assert(other_rmq == s.reconcile_state_of(other_rmq.object_ref()).triggering_cr);
                assert(rabbitmq.spec() == other_rmq.spec());
            }
        }
    }
    invariant_action_n!(
        spec, stronger_next, RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
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
        forall |msg: Message| {
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
        spec.entails(always(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)))),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(every_create_sts_req_does_the_same(rabbitmq))))
        ),
{
    let requirements = |msg: Message, s: RMQCluster| {
        sts_create_request_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_create_request().obj.spec == StatefulSetView::marshal_spec(make_stateful_set(rabbitmq).spec)
        && msg.content.get_create_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    };
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.message_in_flight(msg) || requirements(msg, s)) && #[trigger] s_prime.message_in_flight(msg)
        && msg.dst.is_KubernetesAPI() && msg.content.is_APIRequest() implies requirements(msg, s_prime) by {
            if !s.message_in_flight(msg) && sts_create_request_msg(rabbitmq.object_ref())(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                assert(step.is_ControllerStep());
                let other_rmq = s.reconcile_state_of(step.get_ControllerStep_0().2.get_Some_0()).triggering_cr;
                seq_lemmas::seq_equal_preserved_by_add(
                    other_rmq.metadata.name.get_Some_0(),
                    rabbitmq.metadata.name.get_Some_0(),
                    new_strlit("-server")@
                );
                assert(other_rmq.object_ref() == rabbitmq.object_ref());
                assert(other_rmq == s.reconcile_state_of(other_rmq.object_ref()).triggering_cr);
                assert(rabbitmq.spec() == other_rmq.spec());
            }
        }
    }
    invariant_action_n!(
        spec, stronger_next, RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))
    );
    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(every_create_sts_req_does_the_same(rabbitmq)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn every_create_cm_req_does_the_same(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        forall |msg: Message| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& cm_create_request_msg(rabbitmq.object_ref())(msg)
        } ==> msg.content.get_create_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ()))
            && msg.content.get_create_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    }
}

pub proof fn lemma_true_leads_to_always_every_create_cm_req_does_the_same(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)))),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(every_create_cm_req_does_the_same(rabbitmq))))
        ),
{
    let requirements = |msg: Message, s: RMQCluster| {
        cm_create_request_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_create_request().obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ()))
        && && msg.content.get_create_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    };
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.message_in_flight(msg) || requirements(msg, s)) && #[trigger] s_prime.message_in_flight(msg)
        && msg.dst.is_KubernetesAPI() && msg.content.is_APIRequest() implies requirements(msg, s_prime) by {
            if !s.message_in_flight(msg) && cm_create_request_msg(rabbitmq.object_ref())(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                assert(step.is_ControllerStep());
                let other_rmq = s.reconcile_state_of(step.get_ControllerStep_0().2.get_Some_0()).triggering_cr;

                let other_name = other_rmq.metadata.name.get_Some_0();
                // assert(msg.content.get_create_request().obj.metadata.name.get_Some_0() == other_name + new_strlit("-server-conf")@);
                let this_name = rabbitmq.metadata.name.get_Some_0();
                assert_by(
                    other_name + new_strlit("-plugins-conf")@ != this_name + new_strlit("-server-conf")@,
                    {
                        let str1 = this_name + new_strlit("-server-conf")@;
                        let str2 = other_name + new_strlit("-plugins-conf")@;
                        reveal_strlit("-server-conf");
                        reveal_strlit("-plugins-conf");
                        if str1.len() == str2.len() {
                            assert(str1[str1.len() - 6] == 's');
                            assert(str2[str1.len() - 6] == 'r');
                        }
                    }
                );
                seq_lemmas::seq_equal_preserved_by_add(this_name, other_name, new_strlit("-server-conf")@);
                assert(this_name == other_name);
                assert(rabbitmq.object_ref() == other_rmq.object_ref());
                assert(other_rmq == s.reconcile_state_of(other_rmq.object_ref()).triggering_cr);
                assert(rabbitmq.spec() == other_rmq.spec());
            }
        }
    }
    invariant_action_n!(
        spec, stronger_next, RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq))
    );
    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(every_create_cm_req_does_the_same(rabbitmq)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn pending_msg_at_after_create_stateful_set_step_is_create_sts_req(
    key: ObjectRef
) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateStatefulSet)(s)
        ==> {
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& sts_create_request_msg(key)(s.pending_req_of(key))
        }
    }
}

pub proof fn lemma_always_pending_msg_at_after_create_stateful_set_step_is_create_sts_req(
    spec: TempPred<RMQCluster>, key: ObjectRef
)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(
            always(lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)))
        ),
{
    let invariant = pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key);
    let init = RMQCluster::init();
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
    };

    RMQCluster::lemma_always_each_key_in_reconcile_is_consistent_with_its_object(spec);

    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))
    );

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn pending_msg_at_after_update_stateful_set_step_is_update_sts_req(
    key: ObjectRef
) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s)
        ==> {
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& sts_update_request_msg(key)(s.pending_req_of(key))
        }
    }
}

pub proof fn lemma_always_pending_msg_at_after_update_stateful_set_step_is_update_sts_req(
    spec: TempPred<RMQCluster>, key: ObjectRef
)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(
            always(lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)))
        ),
{
    let invariant = pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key);
    let init = RMQCluster::init();
    let stronger_next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
    };

    RMQCluster::lemma_always_each_key_in_reconcile_is_consistent_with_its_object(spec);

    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))
    );

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn at_most_one_create_sts_req_is_in_flight(key: ObjectRef) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& sts_create_request_msg(key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateStatefulSet)(s)
            &&& msg == s.pending_req_of(key)
            &&& s.network_state.in_flight.count(msg) == 1
        }
    }
}

pub proof fn lemma_true_leads_to_always_at_most_one_create_sts_req_is_in_flight(spec: TempPred<RMQCluster>, key: ObjectRef)
    requires
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)))),
        spec.entails(always(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(at_most_one_create_sts_req_is_in_flight(key))))
        ),
{
    let requirements = |msg: Message, s: RMQCluster| {
        sts_create_request_msg(key)(msg)
        ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateStatefulSet)(s)
            &&& msg == s.pending_req_of(key)
            &&& s.network_state.in_flight.count(msg) == 1
        }
    };
    let stronger_next = |s: RMQCluster, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.message_in_flight(msg) || requirements(msg, s)) && #[trigger] s_prime.message_in_flight(msg)
        implies requirements(msg, s_prime) by {
            if sts_create_request_msg(key)(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                match step {
                    Step::KubernetesAPIStep(input) => {
                        assert(s.message_in_flight(msg));
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateStatefulSet)(s_prime));
                        assert(s_prime.network_state.in_flight.count(msg) == 1);
                    },
                    Step::BuiltinControllersStep(input) => {
                        assert(s.message_in_flight(msg));
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateStatefulSet)(s_prime));
                        assert(s_prime.network_state.in_flight.count(msg) == 1);
                    },
                    Step::ControllerStep(input) => {
                        let cr_key = input.2.get_Some_0();
                        if cr_key != key {
                            if cr_key.name != key.name {
                                seq_lemmas::seq_unequal_preserved_by_add(cr_key.name, key.name, new_strlit("-server")@);
                            }
                            assert(s.message_in_flight(msg));
                            assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                            assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateStatefulSet)(s_prime));
                            assert(s_prime.network_state.in_flight.count(msg) == 1);
                        } else {
                            if s.message_in_flight(msg) {
                                assert(input.0.is_Some());
                                assert(resp_msg_matches_req_msg(input.0.get_Some_0(), s.pending_req_of(key)));
                                assert(false);
                            } else {
                                assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateStatefulSet)(s_prime));
                            }
                        }
                    },
                    Step::ClientStep(input) => {
                        assert(s.message_in_flight(msg));
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterCreateStatefulSet)(s_prime));
                        assert(s_prime.network_state.in_flight.count(msg) == 1);
                    },
                    _ => {}
                }
            }
        }
    }
    invariant_action_n!(
        spec, stronger_next, RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::crash_disabled()), lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key))
    );

    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(at_most_one_create_sts_req_is_in_flight(key)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn at_most_one_update_sts_req_is_in_flight(key: ObjectRef) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& sts_update_request_msg(key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s)
            &&& msg == s.pending_req_of(key)
            &&& s.network_state.in_flight.count(msg) == 1
        }
    }
}

pub proof fn lemma_true_leads_to_always_at_most_one_update_sts_req_is_in_flight(spec: TempPred<RMQCluster>, key: ObjectRef)
    requires
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(at_most_one_update_sts_req_is_in_flight(key))))
        ),
{
    let requirements = |msg: Message, s: RMQCluster| {
        sts_update_request_msg(key)(msg)
        ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s)
            &&& msg == s.pending_req_of(key)
            &&& s.network_state.in_flight.count(msg) == 1
        }
    };
    let stronger_next = |s: RMQCluster, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.message_in_flight(msg) || requirements(msg, s)) && #[trigger] s_prime.message_in_flight(msg)
        implies requirements(msg, s_prime) by {
            if sts_update_request_msg(key)(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                match step {
                    Step::KubernetesAPIStep(input) => {
                        assert(s.message_in_flight(msg));
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s_prime));
                        assert(s_prime.network_state.in_flight.count(msg) == 1);
                    },
                    Step::BuiltinControllersStep(input) => {
                        assert(s.message_in_flight(msg));
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s_prime));
                        assert(s_prime.network_state.in_flight.count(msg) == 1);
                    },
                    Step::ControllerStep(input) => {
                        let cr_key = input.2.get_Some_0();
                        if cr_key != key {
                            if cr_key.name != key.name {
                                seq_lemmas::seq_unequal_preserved_by_add(cr_key.name, key.name, new_strlit("-server")@);
                            }
                            assert(s.message_in_flight(msg));
                            assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                            assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s_prime));
                            assert(s_prime.network_state.in_flight.count(msg) == 1);
                        } else {
                            if s.message_in_flight(msg) {
                                assert(input.0.is_Some());
                                assert(resp_msg_matches_req_msg(input.0.get_Some_0(), s.pending_req_of(key)));
                                assert(false);
                            } else {
                                assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s_prime));
                            }
                        }
                    },
                    Step::ClientStep(input) => {
                        assert(s.message_in_flight(msg));
                        assert(s.reconcile_state_of(key) == s_prime.reconcile_state_of(key));
                        assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s_prime));
                        assert(s_prime.network_state.in_flight.count(msg) == 1);
                    },
                    _ => {}
                }
            }
        }
    }
    invariant_action_n!(
        spec, stronger_next, RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::crash_disabled()), lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_key_in_reconcile_is_consistent_with_its_object()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key))
    );

    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(at_most_one_update_sts_req_is_in_flight(key)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn sts_delete_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_delete_request()
        && msg.content.get_delete_request().key == make_stateful_set_key(key)
}

pub open spec fn no_delete_sts_req_is_in_flight(key: ObjectRef) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: RMQCluster| {
        forall |msg: Message| !{
            &&& #[trigger] s.message_in_flight(msg)
            &&& sts_delete_request_msg(key)(msg)
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
///     s.message_in_flight(msg) in the statepred of final state (no_delete_sts_req_is_in_flight in this lemma, so we can
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
        spec.entails(always(lift_state(stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq))))
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(no_delete_sts_req_is_in_flight(rabbitmq.object_ref()))))
        ),
{
    let key = rabbitmq.object_ref();
    let requirements = |msg: Message, s: RMQCluster| !sts_delete_request_msg(key)(msg);

    let stronger_next = |s: RMQCluster, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::desired_state_is(rabbitmq)(s)
        &&& stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq)(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
    };
    assert forall |s: RMQCluster, s_prime: RMQCluster| #[trigger] stronger_next(s, s_prime) implies RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.message_in_flight(msg) || requirements(msg, s)) && #[trigger] s_prime.message_in_flight(msg)
        implies requirements(msg, s_prime) by {
            if s.resource_key_exists(make_stateful_set_key(key)) {
                let owner_refs = s.resource_obj_of(make_stateful_set_key(key)).metadata.owner_references;
                assert(owner_refs == Some(seq![rabbitmq.controller_owner_ref()]));
                assert(owner_reference_to_object_reference(owner_refs.get_Some_0()[0], key.namespace) == key);
            }
        }
    }
    invariant_action_n!(
        spec, stronger_next, RMQCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements),
        lift_action(RMQCluster::next()), lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq)),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed())
    );

    RMQCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(lift_state(no_delete_sts_req_is_in_flight(key)), lift_state(RMQCluster::every_in_flight_req_msg_satisfies(requirements)));
}

}
