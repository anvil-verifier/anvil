// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::invariants::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::{built_in_controller_req_msg, BuiltinControllerChoice},
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::common::*,
    spec::{rabbitmqcluster::*, reconciler::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

spec fn sts_with_invalid_owner_ref_exists_implies_delete_msg_in_flight(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    let sts_key = make_stateful_set_key(rabbitmq.object_ref());
    |s: RMQCluster| {
        s.resource_key_exists(sts_key)
        && s.resource_obj_of(sts_key).metadata.owner_references != Some(seq![rabbitmq.controller_owner_ref()])
        ==> exists |msg: Message| {
            #[trigger] s.message_in_flight(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_delete_request_with_key(sts_key)
        }
    }
}

#[verifier(external_body)]
pub proof fn lemma_eventually_only_valid_server_config_map_exists(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(server_config_map_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)))),
        spec.entails(always(lift_state(every_update_cm_req_does_the_same(rabbitmq)))),
        spec.entails(always(lift_state(every_create_cm_req_does_the_same(rabbitmq)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(server_config_map_has_owner_reference_pointing_to_current_cr(rabbitmq))))),
{}

pub proof fn lemma_eventually_only_valid_stateful_set_exists(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)))),
        spec.entails(always(lift_state(every_update_sts_req_does_the_same(rabbitmq)))),
        spec.entails(always(lift_state(every_create_sts_req_does_the_same(rabbitmq)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq))))),
{
    let sts_key = make_stateful_set_key(rabbitmq.object_ref());
    let key_exists_and_old_ref = |s: RMQCluster| {
        s.resource_key_exists(sts_key)
        && exists |uid: nat| #![auto]
        uid != rabbitmq.metadata.uid.get_Some_0() && s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref())).metadata.owner_references == Some(seq![OwnerReferenceView {
            block_owner_deletion: None,
            controller: Some(true),
            kind: RabbitmqClusterView::kind(),
            name: rabbitmq.metadata.name.get_Some_0(),
            uid: uid,
        }])
    };
    let delete_msg_in_flight = sts_with_invalid_owner_ref_exists_implies_delete_msg_in_flight(rabbitmq);
    let post = stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq);
    let input = (BuiltinControllerChoice::GarbageCollector, sts_key);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::desired_state_is(rabbitmq)(s)
        &&& stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)(s)
        &&& every_update_sts_req_does_the_same(rabbitmq)(s)
        &&& every_create_sts_req_does_the_same(rabbitmq)(s)
    };
    strengthen_next_n!(
        stronger_next, spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)),
        lift_state(every_update_sts_req_does_the_same(rabbitmq)),
        lift_state(every_create_sts_req_does_the_same(rabbitmq))
    );

    assert forall |s, s_prime: RMQCluster| key_exists_and_old_ref(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::builtin_controllers_next().forward(input)(s, s_prime) implies delete_msg_in_flight(s_prime) by {
        let owner_references = s.resource_obj_of(make_stateful_set_key(rabbitmq.object_ref())).metadata.owner_references.get_Some_0();
        assert(owner_references.len() == 1);
        let new_delete_msg = built_in_controller_req_msg(delete_req_msg_content(
            sts_key, s.rest_id_allocator.allocate().1
        ));
        assert(s_prime.resource_key_exists(sts_key));
        assert(s_prime.message_in_flight(new_delete_msg));
    }

    assert forall |s, s_prime: RMQCluster| key_exists_and_old_ref(s) && #[trigger] stronger_next(s, s_prime) implies key_exists_and_old_ref(s_prime) || delete_msg_in_flight(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::BuiltinControllersStep(i) => {
                if i == input {
                    assert(delete_msg_in_flight(s_prime));
                } else {
                    assert(key_exists_and_old_ref(s_prime));
                }
            },
            Step::KubernetesAPIStep(i) => {
                if i.get_Some_0().content.is_update_request_with_key(sts_key) {
                    if RMQCluster::validate_update_request(i.get_Some_0().content.get_update_request(), s.kubernetes_api_state).is_Some()
                    || RMQCluster::update_is_noop(i.get_Some_0().content.get_update_request().obj, s.resource_obj_of(sts_key)) {
                        assert(key_exists_and_old_ref(s_prime));
                    } else {
                        assert(i.get_Some_0().content.get_update_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()]));
                        StatefulSetView::spec_integrity_is_preserved_by_marshal();
                        assert(!s_prime.resource_key_exists(sts_key) || (s_prime.resource_key_exists(sts_key) && s_prime.resource_obj_of(sts_key).metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])));
                    }
                } else if i.get_Some_0().content.is_delete_request_with_key(sts_key) {
                    assert(s.resource_obj_of(sts_key).metadata.finalizers.is_None());
                    assert(!s_prime.resource_key_exists(sts_key));
                } else {
                    assert(key_exists_and_old_ref(s_prime));
                }
            },
            _ => {
                assert(key_exists_and_old_ref(s_prime) || delete_msg_in_flight(s_prime));
            }
        }
    }

    RMQCluster::lemma_pre_leads_to_post_by_builtin_controllers(
        spec, input, stronger_next, RMQCluster::run_garbage_collector(), key_exists_and_old_ref, delete_msg_in_flight
    );
    partial_implies_and_partial_leads_to_to_leads_to(
        spec,
        lift_state(stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)),
        true_pred(),
        lift_state(key_exists_and_old_ref),
        lift_state(delete_msg_in_flight)
    );
    lemma_delete_msg_in_flight_leads_to_only_valid_sts_exists(spec, rabbitmq);
    leads_to_trans_n!(spec, true_pred(), lift_state(delete_msg_in_flight), lift_state(post));
    leads_to_stable(spec, stronger_next, |s: RMQCluster| true, post);
}

proof fn lemma_delete_msg_in_flight_leads_to_only_valid_sts_exists(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView
)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)))),
        spec.entails(always(lift_state(every_update_sts_req_does_the_same(rabbitmq)))),
        spec.entails(always(lift_state(every_create_sts_req_does_the_same(rabbitmq)))),
    ensures
        spec.entails(lift_state(sts_with_invalid_owner_ref_exists_implies_delete_msg_in_flight(rabbitmq)).leads_to(lift_state(stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq)))),
{
    let pre = sts_with_invalid_owner_ref_exists_implies_delete_msg_in_flight(rabbitmq);
    let post = stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq);
    let sts_key = make_stateful_set_key(rabbitmq.object_ref());
    let key_exists_and_delete_msg_exists = |s: RMQCluster| {
        &&& s.resource_key_exists(sts_key)
        &&& exists |msg: Message| {
            #[trigger] s.message_in_flight(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_delete_request_with_key(sts_key)
        }
    };

    assert_by(
        spec.entails(lift_state(key_exists_and_delete_msg_exists).leads_to(lift_state(post))),
        {
            let msg_to_p = |msg: Message| {
                lift_state(|s: RMQCluster| {
                    &&& s.resource_key_exists(sts_key)
                    &&& s.message_in_flight(msg)
                    &&& msg.dst.is_KubernetesAPI()
                    &&& msg.content.is_delete_request_with_key(sts_key)
                })
            };
            assert forall |msg: Message| spec.entails((#[trigger] msg_to_p(msg)).leads_to(lift_state(post))) by {
                let input = Some(msg);
                let msg_to_p_state = |s: RMQCluster| {
                    &&& s.resource_key_exists(sts_key)
                    &&& s.message_in_flight(msg)
                    &&& msg.dst.is_KubernetesAPI()
                    &&& msg.content.is_delete_request_with_key(sts_key)
                };
                let stronger_next = |s, s_prime: RMQCluster| {
                    &&& RMQCluster::next()(s, s_prime)
                    &&& RMQCluster::busy_disabled()(s)
                    &&& stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)(s)
                    &&& every_update_sts_req_does_the_same(rabbitmq)(s)
                };
                strengthen_next_n!(
                    stronger_next, spec,
                    lift_action(RMQCluster::next()),
                    lift_state(RMQCluster::busy_disabled()),
                    lift_state(stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)),
                    lift_state(every_update_sts_req_does_the_same(rabbitmq))
                );
                RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, RMQCluster::handle_request(), msg_to_p_state, post);
            }
            leads_to_exists_intro(spec, msg_to_p, lift_state(post));
            assert_by(
                tla_exists(msg_to_p) == lift_state(key_exists_and_delete_msg_exists),
                {
                    assert forall |ex| #[trigger] lift_state(key_exists_and_delete_msg_exists).satisfied_by(ex) implies tla_exists(msg_to_p).satisfied_by(ex) by {
                        assert(ex.head().resource_key_exists(sts_key));
                        let msg = choose |msg| {
                            &&& #[trigger] ex.head().message_in_flight(msg)
                            &&& msg.dst.is_KubernetesAPI()
                            &&& msg.content.is_delete_request_with_key(sts_key)
                        };
                        assert(msg_to_p(msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(msg_to_p), lift_state(key_exists_and_delete_msg_exists));
                }
            )
        }
    );
    partial_implies_and_partial_leads_to_to_leads_to(
        spec,
        true_pred(),
        lift_state(pre),
        lift_state(key_exists_and_delete_msg_exists), 
        lift_state(post)
    );
}

}
