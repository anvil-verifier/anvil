// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use crate::zookeeper_controller::{
    model::{reconciler::*, resource::*},
    proof::{helper_invariants, predicate::*, resource::*},
    trusted::{spec_types::*, step::*, zookeeper_api_spec::*},
};
use vstd::{prelude::*, string::*};

verus! {

pub proof fn lemma_from_after_exists_stateful_set_step_to_after_get_stateful_set_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)))),
    ensures
        spec.entails(
            lift_state(pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)))
        ),
{
    lemma_from_after_exists_stateful_set_step_and_key_not_exists_to_after_get_stateful_set_step(spec, zookeeper);
    lemma_from_after_exists_stateful_set_step_and_key_exists_to_after_get_stateful_set_step(spec, zookeeper);
    let key_not_exists = lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)(s)
    });
    let key_exists = lift_state(|s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)(s)
    });
    or_leads_to_combine_temp(spec, key_not_exists, key_exists, lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)));
    temp_pred_equality(key_not_exists.or(key_exists), lift_state(pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)));
}

proof fn lemma_from_after_exists_stateful_set_step_and_key_not_exists_to_after_get_stateful_set_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)))
        ),
{
    let pre = lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)(s)
    });
    let post = lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper));
    let pre_and_req_in_flight = |req_msg| lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_exists_stateful_set_step(zookeeper, req_msg)(s)
    });
    let pre_and_exists_resp_in_flight = lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& at_after_exists_stateful_set_step_and_exists_not_found_resp_in_flight(zookeeper)(s)
    });
    let pre_and_resp_in_flight = |resp_msg| lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& resp_msg_is_the_in_flight_resp_at_after_exists_stateful_set_step(zookeeper, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    });

    assert_by(spec.entails(pre.leads_to(post)), {
        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight)) by {
            lemma_from_pending_req_to_receives_not_found_resp_at_after_exists_stateful_set_step(spec, zookeeper, req_msg);
        }
        leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
        assert_by(tla_exists(pre_and_req_in_flight) == pre, {
            assert forall |ex| #[trigger] pre.satisfied_by(ex) implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
        });

        assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(post)) by {
            lemma_from_at_after_exists_stateful_set_step_to_after_get_stateful_set_step(spec, zookeeper, resp_msg);
        }
        leads_to_exists_intro(spec, pre_and_resp_in_flight, post);
        assert_by(tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight, {
            assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex) implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                    &&& resp_msg.content.get_get_response().res.is_Err()
                    &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
        });

        leads_to_trans_n!(spec, pre, pre_and_exists_resp_in_flight, post);
    });
}

proof fn lemma_from_after_exists_stateful_set_step_and_key_exists_to_after_get_stateful_set_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)))
        ),
{
    let pre = lift_state(|s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)(s)
    });
    let post = lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper));

    let after_exists_zk_node_step_pending = lift_state(|s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& pending_req_in_flight_at_after_exists_zk_node_step(zookeeper)(s)
    });

    assert_by(spec.entails(pre.leads_to(after_exists_zk_node_step_pending)), {
        let after_exists_stateful_set_step_req_msg = |req_msg: ZKMessage| lift_state(|s: ZKCluster| {
            &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
            &&& req_msg_is_the_in_flight_pending_req_at_after_exists_stateful_set_step(zookeeper, req_msg)(s)
        });
        let after_exists_stateful_set_step_waiting = lift_state(|s: ZKCluster| {
            &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
            &&& at_after_exists_stateful_set_step_and_exists_ok_resp_in_flight(zookeeper)(s)
        });
        assert forall |req_msg| spec.entails(#[trigger] after_exists_stateful_set_step_req_msg(req_msg).leads_to(after_exists_stateful_set_step_waiting)) by {
            lemma_from_pending_req_to_receives_ok_resp_at_after_exists_stateful_set_step(spec, zookeeper, req_msg);
        }
        leads_to_exists_intro(spec, after_exists_stateful_set_step_req_msg, after_exists_stateful_set_step_waiting);
        assert_by(tla_exists(after_exists_stateful_set_step_req_msg) == pre, {
            assert forall |ex| #[trigger] pre.satisfied_by(ex) implies tla_exists(after_exists_stateful_set_step_req_msg).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                assert(after_exists_stateful_set_step_req_msg(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(after_exists_stateful_set_step_req_msg), pre);
        });

        let after_exists_stateful_set_step_resp_msg = |resp_msg: ZKMessage| lift_state(|s: ZKCluster| {
            &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_exists_stateful_set_step(zookeeper, resp_msg)(s)
        });
        assert forall |resp_msg| spec.entails(#[trigger] after_exists_stateful_set_step_resp_msg(resp_msg).leads_to(after_exists_zk_node_step_pending)) by {
            lemma_from_after_exists_stateful_set_step_to_after_exists_zk_node_step(spec, zookeeper, resp_msg);
        }
        leads_to_exists_intro(spec, after_exists_stateful_set_step_resp_msg, after_exists_zk_node_step_pending);
        assert_by(tla_exists(after_exists_stateful_set_step_resp_msg) == after_exists_stateful_set_step_waiting, {
            assert forall |ex| #[trigger] after_exists_stateful_set_step_waiting.satisfied_by(ex) implies tla_exists(after_exists_stateful_set_step_resp_msg).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                    &&& resp_msg.content.get_get_response().res.is_Ok()
                };
                assert(after_exists_stateful_set_step_resp_msg(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(after_exists_stateful_set_step_resp_msg), after_exists_stateful_set_step_waiting);
        });

        leads_to_trans_temp(spec, pre, after_exists_stateful_set_step_waiting, after_exists_zk_node_step_pending);
    });

    assert_by(spec.entails(after_exists_zk_node_step_pending.leads_to(post)) , {
        let addr_exists_and_after_exists_zk_node_step_pending = lift_state(|s: ZKCluster| {
            &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
            &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
            &&& pending_req_in_flight_at_after_exists_zk_node_step(zookeeper)(s)
        });
        let addr_not_exists_and_after_exists_zk_node_step_pending = lift_state(|s: ZKCluster| {
            &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
            &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
            &&& pending_req_in_flight_at_after_exists_zk_node_step(zookeeper)(s)
        });

        assert_by(spec.entails(addr_exists_and_after_exists_zk_node_step_pending.leads_to(post)), {
            let after_exists_zk_node_step_req_msg = |req_msg: ZKMessage| lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& req_msg_is_the_in_flight_pending_req_at_after_exists_zk_node_step(zookeeper, req_msg)(s)
            });
            let after_exists_zk_node_step_waiting = lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& at_after_exists_zk_node_step_and_exists_ok_resp_in_flight(zookeeper)(s)
            });
            assert forall |req_msg| spec.entails(#[trigger] after_exists_zk_node_step_req_msg(req_msg).leads_to(after_exists_zk_node_step_waiting)) by {
                lemma_from_pending_req_to_receives_ok_resp_at_after_exists_zk_node_step(spec, zookeeper, req_msg);
            }
            leads_to_exists_intro(spec, after_exists_zk_node_step_req_msg, after_exists_zk_node_step_waiting);
            assert_by(tla_exists(after_exists_zk_node_step_req_msg) == addr_exists_and_after_exists_zk_node_step_pending, {
                assert forall |ex| #[trigger] addr_exists_and_after_exists_zk_node_step_pending.satisfied_by(ex) implies tla_exists(after_exists_zk_node_step_req_msg).satisfied_by(ex) by {
                    let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                    assert(after_exists_zk_node_step_req_msg(req_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(after_exists_zk_node_step_req_msg), addr_exists_and_after_exists_zk_node_step_pending);
            });

            let after_exists_zk_node_step_resp_msg = |resp_msg: ZKMessage| lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& resp_msg_is_the_in_flight_ok_resp_at_after_exists_zk_node_step(zookeeper, resp_msg)(s)
            });
            let after_update_zk_node_step_pending = lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& pending_req_in_flight_at_after_update_zk_node_step(zookeeper)(s)
            });
            assert forall |resp_msg| spec.entails(#[trigger] after_exists_zk_node_step_resp_msg(resp_msg).leads_to(after_update_zk_node_step_pending)) by {
                lemma_from_after_exists_zk_node_step_to_after_update_zk_node_step(spec, zookeeper, resp_msg);
            }
            leads_to_exists_intro(spec, after_exists_zk_node_step_resp_msg, after_update_zk_node_step_pending);
            assert_by(tla_exists(after_exists_zk_node_step_resp_msg) == after_exists_zk_node_step_waiting, {
                assert forall |ex| #[trigger] after_exists_zk_node_step_waiting.satisfied_by(ex) implies tla_exists(after_exists_zk_node_step_resp_msg).satisfied_by(ex) by {
                    let addr = zk_node_addr(ex.head(), zookeeper);
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                        &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::ExistsResponse(ZKAPIExistsResultView{res: Ok(Some(ex.head().external_state().data[addr].1))})
                    };
                    assert(after_exists_zk_node_step_resp_msg(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(after_exists_zk_node_step_resp_msg), after_exists_zk_node_step_waiting);
            });

            let after_update_zk_node_step_req_msg = |req_msg: ZKMessage| lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& req_msg_is_the_in_flight_pending_req_at_after_update_zk_node_step(zookeeper, req_msg)(s)
            });
            let after_update_zk_node_step_waiting = lift_state(at_after_update_zk_node_step_and_exists_ok_resp_in_flight(zookeeper));
            assert forall |req_msg| spec.entails(#[trigger] after_update_zk_node_step_req_msg(req_msg).leads_to(after_update_zk_node_step_waiting)) by {
                lemma_from_pending_req_to_receives_ok_resp_at_after_update_zk_node_step(spec, zookeeper, req_msg);
            }
            leads_to_exists_intro(spec, after_update_zk_node_step_req_msg, after_update_zk_node_step_waiting);
            assert_by(tla_exists(after_update_zk_node_step_req_msg) == after_update_zk_node_step_pending, {
                assert forall |ex| #[trigger] after_update_zk_node_step_pending.satisfied_by(ex) implies tla_exists(after_update_zk_node_step_req_msg).satisfied_by(ex) by {
                    let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                    assert(after_update_zk_node_step_req_msg(req_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(after_update_zk_node_step_req_msg), after_update_zk_node_step_pending);
            });

            let after_update_zk_node_step_resp_msg = |resp_msg: ZKMessage| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_update_zk_node_step(zookeeper, resp_msg));
            assert forall |resp_msg| spec.entails(#[trigger] after_update_zk_node_step_resp_msg(resp_msg).leads_to(post)) by {
                lemma_from_after_update_zk_node_step_to_after_get_stateful_set_step(spec, zookeeper, resp_msg);
            }
            leads_to_exists_intro(spec, after_update_zk_node_step_resp_msg, post);
            assert_by(tla_exists(after_update_zk_node_step_resp_msg) == after_update_zk_node_step_waiting, {
                assert forall |ex| #[trigger] after_update_zk_node_step_waiting.satisfied_by(ex) implies tla_exists(after_update_zk_node_step_resp_msg).satisfied_by(ex) by {
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                        &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::SetDataResponse(ZKAPISetDataResultView{res: Ok(())})
                    };
                    assert(after_update_zk_node_step_resp_msg(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(after_update_zk_node_step_resp_msg), after_update_zk_node_step_waiting);
            });

            leads_to_trans_n!(spec,
                addr_exists_and_after_exists_zk_node_step_pending, after_exists_zk_node_step_waiting,
                after_update_zk_node_step_pending, after_update_zk_node_step_waiting, post
            );
        });

        assert_by(spec.entails(addr_not_exists_and_after_exists_zk_node_step_pending.leads_to(post)), {
            let after_exists_zk_node_step_req_msg = |req_msg: ZKMessage| lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& req_msg_is_the_in_flight_pending_req_at_after_exists_zk_node_step(zookeeper, req_msg)(s)
            });
            let after_exists_zk_node_step_waiting = lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& at_after_exists_zk_node_step_and_exists_not_found_resp_in_flight(zookeeper)(s)
            });
            assert forall |req_msg| spec.entails(#[trigger] after_exists_zk_node_step_req_msg(req_msg).leads_to(after_exists_zk_node_step_waiting)) by {
                lemma_from_pending_req_to_receives_not_found_resp_at_after_exists_zk_node_step(spec, zookeeper, req_msg);
            }
            leads_to_exists_intro(spec, after_exists_zk_node_step_req_msg, after_exists_zk_node_step_waiting);
            assert_by(tla_exists(after_exists_zk_node_step_req_msg) == addr_not_exists_and_after_exists_zk_node_step_pending, {
                assert forall |ex| #[trigger] addr_not_exists_and_after_exists_zk_node_step_pending.satisfied_by(ex) implies tla_exists(after_exists_zk_node_step_req_msg).satisfied_by(ex) by {
                    let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                    assert(after_exists_zk_node_step_req_msg(req_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(after_exists_zk_node_step_req_msg), addr_not_exists_and_after_exists_zk_node_step_pending);
            });

            let after_exists_zk_node_step_resp_msg = |resp_msg: ZKMessage| lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& resp_msg_is_the_in_flight_not_found_resp_at_after_exists_zk_node_step(zookeeper, resp_msg)(s)
            });
            let after_create_zk_parent_node_step_pending = lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& pending_req_in_flight_at_after_create_zk_parent_node_step(zookeeper)(s)
            });
            assert forall |resp_msg| spec.entails(#[trigger] after_exists_zk_node_step_resp_msg(resp_msg).leads_to(after_create_zk_parent_node_step_pending)) by {
                lemma_from_after_exists_zk_node_step_to_after_create_zk_parent_node_step(spec, zookeeper, resp_msg);
            }
            leads_to_exists_intro(spec, after_exists_zk_node_step_resp_msg, after_create_zk_parent_node_step_pending);
            assert_by(tla_exists(after_exists_zk_node_step_resp_msg) == after_exists_zk_node_step_waiting, {
                assert forall |ex| #[trigger] after_exists_zk_node_step_waiting.satisfied_by(ex) implies tla_exists(after_exists_zk_node_step_resp_msg).satisfied_by(ex) by {
                    let addr = zk_node_addr(ex.head(), zookeeper);
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                        &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::ExistsResponse(ZKAPIExistsResultView{res: Ok(None)})
                    };
                    assert(after_exists_zk_node_step_resp_msg(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(after_exists_zk_node_step_resp_msg), after_exists_zk_node_step_waiting);
            });

            let after_create_zk_parent_node_step_req_msg = |req_msg: ZKMessage| lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& req_msg_is_the_in_flight_pending_req_at_after_create_zk_parent_node_step(zookeeper, req_msg)(s)
            });
            let after_create_zk_parent_node_step_waiting = lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
                &&& at_after_create_zk_parent_node_step_and_exists_ok_or_already_exists_resp_in_flight(zookeeper)(s)
            });
            assert forall |req_msg| spec.entails(#[trigger] after_create_zk_parent_node_step_req_msg(req_msg).leads_to(after_create_zk_parent_node_step_waiting)) by {
                lemma_from_pending_req_to_receives_ok_or_already_exists_resp_at_after_create_zk_parent_node_step(spec, zookeeper, req_msg);
            }
            leads_to_exists_intro(spec, after_create_zk_parent_node_step_req_msg, after_create_zk_parent_node_step_waiting);
            assert_by(tla_exists(after_create_zk_parent_node_step_req_msg) == after_create_zk_parent_node_step_pending, {
                assert forall |ex| #[trigger] after_create_zk_parent_node_step_pending.satisfied_by(ex) implies tla_exists(after_create_zk_parent_node_step_req_msg).satisfied_by(ex) by {
                    let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                    assert(after_create_zk_parent_node_step_req_msg(req_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(after_create_zk_parent_node_step_req_msg), after_create_zk_parent_node_step_pending);
            });

            let after_create_zk_parent_node_step_resp_msg = |resp_msg: ZKMessage| lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
                &&& resp_msg_is_the_in_flight_ok_or_already_exists_resp_at_after_create_zk_parent_node_step(zookeeper, resp_msg)(s)
            });
            let after_create_zk_node_step_pending = lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
                &&& pending_req_in_flight_at_after_create_zk_node_step(zookeeper)(s)
            });
            assert forall |resp_msg| spec.entails(#[trigger] after_create_zk_parent_node_step_resp_msg(resp_msg).leads_to(after_create_zk_node_step_pending)) by {
                lemma_from_after_create_zk_parent_node_step_to_after_create_zk_node_step(spec, zookeeper, resp_msg);
            }
            leads_to_exists_intro(spec, after_create_zk_parent_node_step_resp_msg, after_create_zk_node_step_pending);
            assert_by(tla_exists(after_create_zk_parent_node_step_resp_msg) == after_create_zk_parent_node_step_waiting, {
                assert forall |ex| #[trigger] after_create_zk_parent_node_step_waiting.satisfied_by(ex) implies tla_exists(after_create_zk_parent_node_step_resp_msg).satisfied_by(ex) by {
                    let addr = zk_node_addr(ex.head(), zookeeper);
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                        &&& (resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Ok(())})
                            || resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Err(ZKAPIError::ZKNodeCreateAlreadyExists)}))
                    };
                    assert(after_create_zk_parent_node_step_resp_msg(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(after_create_zk_parent_node_step_resp_msg), after_create_zk_parent_node_step_waiting);
            });

            let after_create_zk_node_step_req_msg = |req_msg: ZKMessage| lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
                &&& req_msg_is_the_in_flight_pending_req_at_after_create_zk_node_step(zookeeper, req_msg)(s)
            });
            let after_create_zk_node_step_waiting = lift_state(at_after_create_zk_node_step_and_exists_ok_resp_in_flight(zookeeper));
            assert forall |req_msg| spec.entails(#[trigger] after_create_zk_node_step_req_msg(req_msg).leads_to(after_create_zk_node_step_waiting)) by {
                lemma_from_pending_req_to_receives_ok_resp_at_after_create_zk_node_step(spec, zookeeper, req_msg);
            }
            leads_to_exists_intro(spec, after_create_zk_node_step_req_msg, after_create_zk_node_step_waiting);
            assert_by(tla_exists(after_create_zk_node_step_req_msg) == after_create_zk_node_step_pending, {
                assert forall |ex| #[trigger] after_create_zk_node_step_pending.satisfied_by(ex) implies tla_exists(after_create_zk_node_step_req_msg).satisfied_by(ex) by {
                    let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                    assert(after_create_zk_node_step_req_msg(req_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(after_create_zk_node_step_req_msg), after_create_zk_node_step_pending);
            });

            let after_create_zk_node_step_resp_msg = |resp_msg: ZKMessage| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_create_zk_node_step(zookeeper, resp_msg));
            assert forall |resp_msg| spec.entails(#[trigger] after_create_zk_node_step_resp_msg(resp_msg).leads_to(post)) by {
                lemma_from_after_create_zk_node_step_to_after_get_stateful_set_step(spec, zookeeper, resp_msg);
            }
            leads_to_exists_intro(spec, after_create_zk_node_step_resp_msg, post);
            assert_by(tla_exists(after_create_zk_node_step_resp_msg) == after_create_zk_node_step_waiting, {
                assert forall |ex| #[trigger] after_create_zk_node_step_waiting.satisfied_by(ex) implies tla_exists(after_create_zk_node_step_resp_msg).satisfied_by(ex) by {
                    let addr = zk_node_addr(ex.head(), zookeeper);
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                        &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Ok(())})
                    };
                    assert(after_create_zk_node_step_resp_msg(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(after_create_zk_node_step_resp_msg), after_create_zk_node_step_waiting);
            });

            leads_to_trans_n!(spec,
                addr_not_exists_and_after_exists_zk_node_step_pending, after_exists_zk_node_step_waiting,
                after_create_zk_parent_node_step_pending, after_create_zk_parent_node_step_waiting,
                after_create_zk_node_step_pending, after_create_zk_node_step_waiting, post
            );
        });

        or_leads_to_combine_temp(spec, addr_exists_and_after_exists_zk_node_step_pending, addr_not_exists_and_after_exists_zk_node_step_pending, post);
        temp_pred_equality(addr_exists_and_after_exists_zk_node_step_pending.or(addr_not_exists_and_after_exists_zk_node_step_pending), after_exists_zk_node_step_pending);
    });
    leads_to_trans_temp(spec, pre, after_exists_zk_node_step_pending, post);
}

proof fn lemma_from_pending_req_to_receives_not_found_resp_at_after_exists_stateful_set_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, req_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& req_msg_is_the_in_flight_pending_req_at_after_exists_stateful_set_step(zookeeper, req_msg)(s)
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                    &&& at_after_exists_stateful_set_step_and_exists_not_found_resp_in_flight(zookeeper)(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_exists_stateful_set_step(zookeeper, req_msg)(s)
    };
    let post = |s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& at_after_exists_stateful_set_step_and_exists_not_found_resp_in_flight(zookeeper)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                assert(!resource_create_request_msg(get_request(SubResource::StatefulSet, zookeeper).key)(input.get_Some_0()));
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Err()
                        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                    });
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        });
    }
    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, ZKCluster::handle_request(), pre, post);
}

proof fn lemma_from_at_after_exists_stateful_set_step_to_after_get_stateful_set_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, resp_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& resp_msg_is_the_in_flight_resp_at_after_exists_stateful_set_step(zookeeper, resp_msg)(s)
                &&& resp_msg.content.get_get_response().res.is_Err()
                &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
            })
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)))
        ),
{
    let pre = |s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& resp_msg_is_the_in_flight_resp_at_after_exists_stateful_set_step(zookeeper, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    };
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper);
    let input = (Some(resp_msg), Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
                assert(!resource_create_request_msg(sts_key)(input.get_Some_0()));
            },
            _ => {}
        }
    }

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

proof fn lemma_from_pending_req_to_receives_ok_resp_at_after_exists_stateful_set_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, req_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& req_msg_is_the_in_flight_pending_req_at_after_exists_stateful_set_step(zookeeper, req_msg)(s)
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                    &&& at_after_exists_stateful_set_step_and_exists_ok_resp_in_flight(zookeeper)(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_exists_stateful_set_step(zookeeper, req_msg)(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& at_after_exists_stateful_set_step_and_exists_ok_resp_in_flight(zookeeper)(s)
    };
    let resource_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
        match step {
            Step::ApiServerStep(input) => {
                assert(!resource_delete_request_msg(sts_key)(input.get_Some_0()));
                assert(!resource_update_request_msg(sts_key)(input.get_Some_0()));
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Ok()
                        &&& resp_msg.content.get_get_response().res.get_Ok_0() == s_prime.resources()[resource_key]
                    });
                    assert(post(s_prime));
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == s_prime.resources()[resource_key]
        });
    }
    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, ZKCluster::handle_request(), pre, post);
}

proof fn lemma_from_after_exists_stateful_set_step_to_after_exists_zk_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, resp_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& resp_msg_is_the_in_flight_ok_resp_at_after_exists_stateful_set_step(zookeeper, resp_msg)(s)
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                    &&& pending_req_in_flight_at_after_exists_zk_node_step(zookeeper)(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_exists_stateful_set_step(zookeeper, resp_msg)(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& pending_req_in_flight_at_after_exists_zk_node_step(zookeeper)(s)
    };
    let input = (Some(resp_msg), Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())(s)
        &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
                assert(!resource_delete_request_msg(sts_key)(input.get_Some_0()));
                assert(!resource_update_request_msg(sts_key)(input.get_Some_0()));
            },
            _ => {}
        }
    }

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

proof fn lemma_from_pending_req_to_receives_ok_resp_at_after_exists_zk_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, req_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& req_msg_is_the_in_flight_pending_req_at_after_exists_zk_node_step(zookeeper, req_msg)(s)
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                    &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                    &&& at_after_exists_zk_node_step_and_exists_ok_resp_in_flight(zookeeper)(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& req_msg_is_the_in_flight_pending_req_at_after_exists_zk_node_step(zookeeper, req_msg)(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& at_after_exists_zk_node_step_and_exists_ok_resp_in_flight(zookeeper)(s)
    };
    let resource_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ExternalAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_external_request_helper(req_msg, s.external_api_state, s.resources()).1;
                    let addr = zk_node_addr(s_prime, zookeeper);
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.is_ExternalAPIResponse()
                        &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::ExistsResponse(ZKAPIExistsResultView{res: Ok(Some(s_prime.external_state().data[addr].1))})
                    });
                    assert(post(s_prime));
                }
            },
            Step::ApiServerStep(input) => {
                assert(!resource_delete_request_msg(resource_key)(input.get_Some_0()));
                assert(!resource_update_request_msg(resource_key)(input.get_Some_0()));
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::external_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_external_request_helper(req_msg, s.external_api_state, s.resources()).1;
        let addr = zk_node_addr(s_prime, zookeeper);
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_ExternalAPIResponse()
            &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::ExistsResponse(ZKAPIExistsResultView{res: Ok(Some(s_prime.external_state().data[addr].1))})
        });
    }

    ZKCluster::lemma_pre_leads_to_post_by_external_api(spec, input, stronger_next, ZKCluster::handle_external_request(), pre, post);
}

proof fn lemma_from_after_exists_zk_node_step_to_after_update_zk_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, resp_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& resp_msg_is_the_in_flight_ok_resp_at_after_exists_zk_node_step(zookeeper, resp_msg)(s)
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                    &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                    &&& pending_req_in_flight_at_after_update_zk_node_step(zookeeper)(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_exists_zk_node_step(zookeeper, resp_msg)(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& pending_req_in_flight_at_after_update_zk_node_step(zookeeper)(s)
    };
    let input = (Some(resp_msg), Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())(s)
        &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
        match step {
            Step::ApiServerStep(input) => {
                assert(!resource_delete_request_msg(sts_key)(input.get_Some_0()));
                assert(!resource_update_request_msg(sts_key)(input.get_Some_0()));
            },
            _ => {}
        }
    }

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

proof fn lemma_from_pending_req_to_receives_ok_resp_at_after_update_zk_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, req_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& req_msg_is_the_in_flight_pending_req_at_after_update_zk_node_step(zookeeper, req_msg)(s)
            })
                .leads_to(lift_state(at_after_update_zk_node_step_and_exists_ok_resp_in_flight(zookeeper)))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& req_msg_is_the_in_flight_pending_req_at_after_update_zk_node_step(zookeeper, req_msg)(s)
    };
    let post = at_after_update_zk_node_step_and_exists_ok_resp_in_flight(zookeeper);
    let resource_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
        match step {
            Step::ExternalAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_external_request_helper(req_msg, s.external_api_state, s.resources()).1;
                    let addr = zk_node_addr(s_prime, zookeeper);
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.is_ExternalAPIResponse()
                        &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::SetDataResponse(ZKAPISetDataResultView{res: Ok(())})
                    });
                    assert(post(s_prime));
                }
            },
            Step::ApiServerStep(input) => {
                assert(!resource_delete_request_msg(sts_key)(input.get_Some_0()));
                assert(!resource_update_request_msg(sts_key)(input.get_Some_0()));
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::external_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_external_request_helper(req_msg, s.external_api_state, s.resources()).1;
        let addr = zk_node_addr(s_prime, zookeeper);
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_ExternalAPIResponse()
            &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::SetDataResponse(ZKAPISetDataResultView{res: Ok(())})
        });
    }

    ZKCluster::lemma_pre_leads_to_post_by_external_api(spec, input, stronger_next, ZKCluster::handle_external_request(), pre, post);
}

proof fn lemma_from_after_update_zk_node_step_to_after_get_stateful_set_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, resp_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_update_zk_node_step(zookeeper, resp_msg))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)))
        ),
{
    let pre = resp_msg_is_the_in_flight_ok_resp_at_after_update_zk_node_step(zookeeper, resp_msg);
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper);
    let input = (Some(resp_msg), Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())(s)
        &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper))
    );

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

proof fn lemma_from_pending_req_to_receives_not_found_resp_at_after_exists_zk_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, req_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& req_msg_is_the_in_flight_pending_req_at_after_exists_zk_node_step(zookeeper, req_msg)(s)
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                    &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                    &&& at_after_exists_zk_node_step_and_exists_not_found_resp_in_flight(zookeeper)(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& req_msg_is_the_in_flight_pending_req_at_after_exists_zk_node_step(zookeeper, req_msg)(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& at_after_exists_zk_node_step_and_exists_not_found_resp_in_flight(zookeeper)(s)
    };
    let resource_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
        match step {
            Step::ExternalAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_external_request_helper(req_msg, s.external_api_state, s.resources()).1;
                    let addr = zk_node_addr(s_prime, zookeeper);
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.is_ExternalAPIResponse()
                        &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::ExistsResponse(ZKAPIExistsResultView{res: Ok(None)})
                    });
                    assert(post(s_prime));
                }
            },
            Step::ApiServerStep(input) => {
                assert(!resource_delete_request_msg(sts_key)(input.get_Some_0()));
                assert(!resource_update_request_msg(sts_key)(input.get_Some_0()));
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::external_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_external_request_helper(req_msg, s.external_api_state, s.resources()).1;
        let addr = zk_node_addr(s_prime, zookeeper);
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_ExternalAPIResponse()
            &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::ExistsResponse(ZKAPIExistsResultView{res: Ok(None)})
        });
    }

    ZKCluster::lemma_pre_leads_to_post_by_external_api(spec, input, stronger_next, ZKCluster::handle_external_request(), pre, post);
}

proof fn lemma_from_after_exists_zk_node_step_to_after_create_zk_parent_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, resp_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& resp_msg_is_the_in_flight_not_found_resp_at_after_exists_zk_node_step(zookeeper, resp_msg)(s)
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                    &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                    &&& pending_req_in_flight_at_after_create_zk_parent_node_step(zookeeper)(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& resp_msg_is_the_in_flight_not_found_resp_at_after_exists_zk_node_step(zookeeper, resp_msg)(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& pending_req_in_flight_at_after_create_zk_parent_node_step(zookeeper)(s)
    };
    let input = (Some(resp_msg), Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())(s)
        &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
                assert(!resource_delete_request_msg(sts_key)(input.get_Some_0()));
                assert(!resource_update_request_msg(sts_key)(input.get_Some_0()));
            },
            _ => {}
        }
    }

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

proof fn lemma_from_pending_req_to_receives_ok_or_already_exists_resp_at_after_create_zk_parent_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, req_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& req_msg_is_the_in_flight_pending_req_at_after_create_zk_parent_node_step(zookeeper, req_msg)(s)
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                    &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                    &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
                    &&& at_after_create_zk_parent_node_step_and_exists_ok_or_already_exists_resp_in_flight(zookeeper)(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_zk_parent_node_step(zookeeper, req_msg)(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
        &&& at_after_create_zk_parent_node_step_and_exists_ok_or_already_exists_resp_in_flight(zookeeper)(s)
    };
    let resource_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ExternalAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_external_request_helper(req_msg, s.external_api_state, s.resources()).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.is_ExternalAPIResponse()
                        &&& (resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Ok(())})
                            || resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Err(ZKAPIError::ZKNodeCreateAlreadyExists)}))
                    });
                    assert(post(s_prime));
                }
            },
            Step::ApiServerStep(input) => {
                let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
                assert(!resource_delete_request_msg(sts_key)(input.get_Some_0()));
                assert(!resource_update_request_msg(sts_key)(input.get_Some_0()));
            }
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::external_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_external_request_helper(req_msg, s.external_api_state, s.resources()).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_ExternalAPIResponse()
            &&& (resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Ok(())})
                || resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Err(ZKAPIError::ZKNodeCreateAlreadyExists)}))
        });
    }

    ZKCluster::lemma_pre_leads_to_post_by_external_api(spec, input, stronger_next, ZKCluster::handle_external_request(), pre, post);
}

proof fn lemma_from_after_create_zk_parent_node_step_to_after_create_zk_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, resp_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
                &&& resp_msg_is_the_in_flight_ok_or_already_exists_resp_at_after_create_zk_parent_node_step(zookeeper, resp_msg)(s)
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                    &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                    &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
                    &&& pending_req_in_flight_at_after_create_zk_node_step(zookeeper)(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
        &&& resp_msg_is_the_in_flight_ok_or_already_exists_resp_at_after_create_zk_parent_node_step(zookeeper, resp_msg)(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
        &&& pending_req_in_flight_at_after_create_zk_node_step(zookeeper)(s)
    };
    let input = (Some(resp_msg), Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())(s)
        &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
        match step {
            Step::ApiServerStep(input) => {
                assert(!resource_delete_request_msg(sts_key)(input.get_Some_0()));
                assert(!resource_update_request_msg(sts_key)(input.get_Some_0()));
            },
            _ => {}
        }
    }

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

proof fn lemma_from_pending_req_to_receives_ok_resp_at_after_create_zk_node_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, req_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
                &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
                &&& req_msg_is_the_in_flight_pending_req_at_after_create_zk_node_step(zookeeper, req_msg)(s)
            }).leads_to(lift_state(at_after_create_zk_node_step_and_exists_ok_resp_in_flight(zookeeper)))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& !s.external_state().data.contains_key(zk_node_addr(s, zookeeper))
        &&& s.external_state().data.contains_key(zk_parent_node_addr(s, zookeeper))
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_zk_node_step(zookeeper, req_msg)(s)
    };
    let post = at_after_create_zk_node_step_and_exists_ok_resp_in_flight(zookeeper);
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::ConfigMap, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
        match step {
            Step::ExternalAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_external_request_helper(req_msg, s.external_api_state, s.resources()).1;
                    assert(zk_parent_node_addr(s, zookeeper).path =~= zk_node_addr(s, zookeeper).parent_addr().path);
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.is_ExternalAPIResponse()
                        &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Ok(())})
                    });
                    assert(post(s_prime));
                }
            },
            Step::ApiServerStep(input) => {
                assert(!resource_delete_request_msg(sts_key)(input.get_Some_0()));
                assert(!resource_update_request_msg(sts_key)(input.get_Some_0()));
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::external_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_external_request_helper(req_msg, s.external_api_state, s.resources()).1;
        assert(zk_parent_node_addr(s, zookeeper).path =~= zk_node_addr(s, zookeeper).parent_addr().path);
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_ExternalAPIResponse()
            &&& resp_msg.content.get_ExternalAPIResponse_0() == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Ok(())})
        });
    }

    ZKCluster::lemma_pre_leads_to_post_by_external_api(spec, input, stronger_next, ZKCluster::handle_external_request(), pre, post);
}

proof fn lemma_from_after_create_zk_node_step_to_after_get_stateful_set_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, resp_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_create_zk_node_step(zookeeper, resp_msg))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)))
        ),
{
    let pre = resp_msg_is_the_in_flight_ok_resp_at_after_create_zk_node_step(zookeeper, resp_msg);
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper);
    let input = (Some(resp_msg), Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())(s)
        &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id())
    );

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}


}
