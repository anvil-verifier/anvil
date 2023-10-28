// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, error::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use crate::zookeeper_controller::{
    common::*,
    proof::{
        helper_invariants::the_object_in_reconcile_satisfies_state_validation, predicate::*,
        resource::*,
    },
    spec::{reconciler::*, types::*, zookeeper_api::*},
};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub open spec fn stateful_set_has_at_least_one_replica(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = get_request(SubResource::StatefulSet, zookeeper).key;
        s.resources().contains_key(key) ==> {
            &&& StatefulSetView::unmarshal(s.resources()[key]).is_Ok()
            &&& StatefulSetView::unmarshal(s.resources()[key]).get_Ok_0().spec.is_Some()
            &&& StatefulSetView::unmarshal(s.resources()[key]).get_Ok_0().spec.get_Some_0().replicas.is_Some()
            &&& StatefulSetView::unmarshal(s.resources()[key]).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() > 0
        }
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_stateful_set_has_at_least_one_replica(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(the_object_in_reconcile_satisfies_state_validation()))),
    ensures
        spec.entails(always(lift_state(stateful_set_has_at_least_one_replica(zookeeper)))),
{
    lemma_always_stateful_set_in_create_req_has_at_least_one_replica(spec, zookeeper);
    lemma_always_stateful_set_in_update_req_has_at_least_one_replica(spec, zookeeper);
    let inv = stateful_set_has_at_least_one_replica(zookeeper);
    let next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& stateful_set_in_create_req_has_at_least_one_replica(zookeeper)(s)
        &&& stateful_set_in_update_req_has_at_least_one_replica(zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(stateful_set_in_create_req_has_at_least_one_replica(zookeeper)),
        lift_state(stateful_set_in_update_req_has_at_least_one_replica(zookeeper))
    );
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        StatefulSetView::marshal_spec_preserves_integrity();
        StatefulSetView::marshal_status_preserves_integrity();
    }
    init_invariant(spec, ZKCluster::init(), next, inv);
}

pub open spec fn stateful_set_in_create_req_has_at_least_one_replica(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = get_request(SubResource::StatefulSet, zookeeper).key;
        forall |msg: ZKMessage| {
            &&& s.network_state.in_flight.contains(msg)
            &&& resource_create_request_msg(key)(msg)
        } ==> {
            let obj = msg.content.get_create_request().obj;
            &&& StatefulSetView::unmarshal(obj).is_Ok()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.is_Some()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() > 0
        }
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_always_stateful_set_in_create_req_has_at_least_one_replica(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(the_object_in_reconcile_satisfies_state_validation()))),
    ensures
        spec.entails(always(lift_state(stateful_set_in_create_req_has_at_least_one_replica(zookeeper)))),
{
    let inv = stateful_set_in_create_req_has_at_least_one_replica(zookeeper);
    let next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& the_object_in_reconcile_satisfies_state_validation()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(the_object_in_reconcile_satisfies_state_validation())
    );
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = get_request(SubResource::StatefulSet, zookeeper).key;
        assert forall |msg: ZKMessage| {
            &&& s_prime.network_state.in_flight.contains(msg)
            &&& resource_create_request_msg(key)(msg)
        } implies {
            let obj = msg.content.get_create_request().obj;
            &&& StatefulSetView::unmarshal(obj).is_Ok()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.is_Some()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() > 0
        } by {
            let post = {
                let obj = msg.content.get_create_request().obj;
                &&& StatefulSetView::unmarshal(obj).is_Ok()
                &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
                &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.is_Some()
                &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() > 0
            };
            if !s.network_state.in_flight.contains(msg) {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        let cr_key = input.1.get_Some_0();
                        assert(s.ongoing_reconciles().contains_key(cr_key));
                        if cr_key == zookeeper.object_ref() {
                            assert(s.ongoing_reconciles()[cr_key].triggering_cr.state_validation());
                            StatefulSetView::marshal_spec_preserves_integrity();
                            StatefulSetView::marshal_status_preserves_integrity();
                            assert(post);
                        } else {
                            assert(false);
                        }
                    },
                    _ => { assert(false); }
                }
            }
        }
    }
    init_invariant(spec, ZKCluster::init(), next, inv);
}

pub open spec fn stateful_set_in_update_req_has_at_least_one_replica(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = get_request(SubResource::StatefulSet, zookeeper).key;
        forall |msg: ZKMessage| {
            &&& s.network_state.in_flight.contains(msg)
            &&& resource_update_request_msg(key)(msg)
        } ==> {
            let obj = msg.content.get_update_request().obj;
            &&& StatefulSetView::unmarshal(obj).is_Ok()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.is_Some()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() > 0
        }
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_always_stateful_set_in_update_req_has_at_least_one_replica(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(the_object_in_reconcile_satisfies_state_validation()))),
    ensures
        spec.entails(always(lift_state(stateful_set_in_update_req_has_at_least_one_replica(zookeeper)))),
{
    let inv = stateful_set_in_update_req_has_at_least_one_replica(zookeeper);
    let next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& the_object_in_reconcile_satisfies_state_validation()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(the_object_in_reconcile_satisfies_state_validation())
    );
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = get_request(SubResource::StatefulSet, zookeeper).key;
        assert forall |msg: ZKMessage| {
            &&& s_prime.network_state.in_flight.contains(msg)
            &&& resource_update_request_msg(key)(msg)
        } implies {
            let obj = msg.content.get_update_request().obj;
            &&& StatefulSetView::unmarshal(obj).is_Ok()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.is_Some()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() > 0
        } by {
            let post = {
                let obj = msg.content.get_update_request().obj;
                &&& StatefulSetView::unmarshal(obj).is_Ok()
                &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
                &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.is_Some()
                &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() > 0
            };
            if !s.network_state.in_flight.contains(msg) {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        let cr_key = input.1.get_Some_0();
                        assert(s.ongoing_reconciles().contains_key(cr_key));
                        if cr_key == zookeeper.object_ref() {
                            StatefulSetView::marshal_spec_preserves_integrity();
                            StatefulSetView::marshal_status_preserves_integrity();
                            assert(s.ongoing_reconciles()[cr_key].triggering_cr.state_validation());
                            assert(post);
                        } else {
                            assert(false);
                        }
                    },
                    _ => { assert(false); }
                }
            }
        }
    }
    init_invariant(spec, ZKCluster::init(), next, inv);
}


pub open spec fn every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = zookeeper.object_ref();
        forall |msg: ZKMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& zk_set_data_request_msg(zookeeper)(msg)
        } ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterUpdateZKNode)(s)
            &&& ZKCluster::pending_req_msg_is(s, key, msg)
        }
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_every_zk_set_data_request_implies_at_after_update_zk_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)))),
        spec.entails(always(lift_state(ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper))))
        ),
{
    let key = zookeeper.object_ref();
    let requirements = |msg: ZKMessage, s: ZKCluster| {
        zk_set_data_request_msg(zookeeper)(msg) ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterUpdateZKNode)(s)
            &&& ZKCluster::pending_req_msg_is(s, key, msg)
        }
    };
    let stronger_next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)(s)
        &&& ZKCluster::every_in_flight_req_is_unique()(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: ZKMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if zk_set_data_request_msg(zookeeper)(msg) {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_zk_request_implies_step_helper(zookeeper, s, s_prime, msg, step);
                    let resp = step.get_ControllerStep_0().0.get_Some_0();
                    assert(s.in_flight().contains(resp));
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(ZKCluster::next()), lift_state(ZKCluster::crash_disabled()), lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper))
    );

    ZKCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)),
        lift_state(ZKCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}


pub open spec fn every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = zookeeper.object_ref();
        forall |msg: ZKMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& zk_create_node_request_msg(zookeeper)(msg)
        } ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterCreateZKNode)(s)
            &&& ZKCluster::pending_req_msg_is(s, key, msg)
        }
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_every_zk_create_node_request_implies_at_after_create_zk_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)))),
        spec.entails(always(lift_state(ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())))
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper))))
        ),
{
    let key = zookeeper.object_ref();
    let requirements = |msg: ZKMessage, s: ZKCluster| {
        zk_create_node_request_msg(zookeeper)(msg) ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterCreateZKNode)(s)
            &&& ZKCluster::pending_req_msg_is(s, key, msg)
        }
    };
    let stronger_next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)(s)
        &&& ZKCluster::every_in_flight_req_is_unique()(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: ZKMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if zk_create_node_request_msg(zookeeper)(msg) {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_zk_request_implies_step_helper(zookeeper, s, s_prime, msg, step);
                    let resp = step.get_ControllerStep_0().0.get_Some_0();
                    assert(s.in_flight().contains(resp));
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(ZKCluster::next()), lift_state(ZKCluster::crash_disabled()), lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper))
    );

    ZKCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)),
        lift_state(ZKCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

#[verifier(spinoff_prover)]
pub proof fn lemma_zk_request_implies_step_helper(zookeeper: ZookeeperClusterView, s: ZKCluster, s_prime: ZKCluster, msg: ZKMessage, step: ZKStep)
    requires
        !s.in_flight().contains(msg), s_prime.in_flight().contains(msg),
        ZKCluster::next_step(s, s_prime, step),
        ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
    ensures
        zk_set_data_request_msg(zookeeper)(msg)
        ==> step.is_ControllerStep() && step.get_ControllerStep_0().1.get_Some_0() == zookeeper.object_ref()
            && at_zk_step(zookeeper.object_ref(), ZookeeperReconcileStep::AfterExistsZKNode)(s)
            && at_zk_step(zookeeper.object_ref(), ZookeeperReconcileStep::AfterUpdateZKNode)(s_prime)
            && ZKCluster::pending_req_msg_is(s_prime, zookeeper.object_ref(), msg),
        zk_create_node_request_msg(zookeeper)(msg)
        ==> step.is_ControllerStep() && step.get_ControllerStep_0().1.get_Some_0() == zookeeper.object_ref()
            && at_zk_step(zookeeper.object_ref(), ZookeeperReconcileStep::AfterCreateZKParentNode)(s)
            && at_zk_step(zookeeper.object_ref(), ZookeeperReconcileStep::AfterCreateZKNode)(s_prime)
            && ZKCluster::pending_req_msg_is(s_prime, zookeeper.object_ref(), msg),
{
    let cr_key = step.get_ControllerStep_0().1.get_Some_0();
    let key = zookeeper.object_ref();
    let cr = s.ongoing_reconciles()[key].triggering_cr;
    if zk_set_data_request_msg(zookeeper)(msg) {
        assert(step.is_ControllerStep());
        assert(s.ongoing_reconciles().contains_key(cr_key));
        let local_step = s.ongoing_reconciles()[cr_key].local_state.reconcile_step;
        let local_step_prime = s_prime.ongoing_reconciles()[cr_key].local_state.reconcile_step;
        assert(cr_key == zookeeper.object_ref());
        assert(ZKCluster::pending_req_msg_is(s_prime, cr_key, msg));
        assert(local_step_prime.is_AfterUpdateZKNode());
        assert(local_step.is_AfterExistsZKNode());
    } else if zk_create_node_request_msg(zookeeper)(msg) {
        assert(step.is_ControllerStep());
        assert(s.ongoing_reconciles().contains_key(cr_key));
        let local_step = s.ongoing_reconciles()[cr_key].local_state.reconcile_step;
        let local_step_prime = s_prime.ongoing_reconciles()[cr_key].local_state.reconcile_step;
        assert(cr_key == zookeeper.object_ref());
        assert(ZKCluster::pending_req_msg_is(s_prime, cr_key, msg));
        assert(!(zk_node_path(zookeeper) =~= zk_parent_node_path(zookeeper)));
        assert(local_step_prime.is_AfterCreateZKNode());
        assert(local_step.is_AfterCreateZKParentNode());
    }
}


}
