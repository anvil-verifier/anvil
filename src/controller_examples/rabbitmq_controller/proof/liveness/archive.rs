// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::{common::*, helper_invariants},
    spec::{reconciler::*, types::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// We prove init /\ []next /\ []wf |= []RMQCluster::desired_state_is(rabbitmq) ~> []current_state_matches(rabbitmq) holds for each rabbitmq.
proof fn liveness_proof_forall_rabbitmq()
    ensures
        forall |rabbitmq: RabbitmqClusterView| rabbitmq.well_formed() ==> #[trigger] cluster_spec().entails(liveness(rabbitmq)),
{
    assert forall |rabbitmq: RabbitmqClusterView| rabbitmq.well_formed()
    implies #[trigger] cluster_spec().entails(liveness(rabbitmq)) by {
        liveness_proof(rabbitmq);
    };
}

proof fn liveness_proof(rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
    ensures
        cluster_spec().entails(liveness(rabbitmq)),
{
    lemma_true_leads_to_always_current_state_matches_rabbitmq_under_eventual_invariants(rabbitmq);

    always_p_is_stable(lift_state(RMQCluster::desired_state_is(rabbitmq)));
    invariants_is_stable(rabbitmq);
    invariants_since_phase_I_is_stable(rabbitmq);
    invariants_since_phase_II_is_stable(rabbitmq);
    invariants_since_phase_III_is_stable(rabbitmq);
    invariants_since_phase_IV_is_stable(rabbitmq);
    stable_and_n!(
        invariants(rabbitmq),
        always(lift_state(RMQCluster::desired_state_is(rabbitmq))),
        invariants_since_phase_I(rabbitmq),
        invariants_since_phase_II(rabbitmq),
        invariants_since_phase_III(rabbitmq),
        invariants_since_phase_IV(rabbitmq)
    );
    // Eliminate all the invariants by phase.
    assert_by(
        invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq)).and(invariants_since_phase_III(rabbitmq)).and(invariants_since_phase_IV(rabbitmq))
        .entails(
            true_pred().leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq)).and(invariants_since_phase_III(rabbitmq)).and(invariants_since_phase_IV(rabbitmq));
            unpack_conditions_from_spec(spec, invariants_since_phase_V(rabbitmq), true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(invariants_since_phase_V(rabbitmq)), invariants_since_phase_V(rabbitmq));
            eliminate_always(spec, lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()));
            helper_invariants::lemma_true_leads_to_always_no_delete_sts_req_is_in_flight(spec, rabbitmq);
            helper_invariants::lemma_true_leads_to_always_no_delete_cm_req_is_in_flight(spec, rabbitmq);
            leads_to_always_combine_temp(
                spec, true_pred(),
                lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(make_stateful_set_key(rabbitmq.object_ref()))),
                lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(make_server_config_map_key(rabbitmq.object_ref())))
            );
            leads_to_trans_temp(spec, true_pred(), invariants_since_phase_V(rabbitmq), always(current_state_matches(rabbitmq)));
        }
    );
    assert_by(
        invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq)).and(invariants_since_phase_III(rabbitmq))
        .entails(
            true_pred().leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq)).and(invariants_since_phase_III(rabbitmq));
            unpack_conditions_from_spec(spec, invariants_since_phase_IV(rabbitmq), true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(invariants_since_phase_IV(rabbitmq)), invariants_since_phase_IV(rabbitmq));
            helper_invariants::lemma_eventually_only_valid_stateful_set_exists(spec, rabbitmq);
            helper_invariants::lemma_eventually_only_valid_server_config_map_exists(spec, rabbitmq);
            leads_to_always_combine_temp(
                spec, true_pred(),
                lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq)),
                lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq))
            );
            leads_to_trans_temp(spec, true_pred(), invariants_since_phase_IV(rabbitmq), always(current_state_matches(rabbitmq)));
        }
    );
    assert_by(
        invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq)).entails(
            true_pred().leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).and(invariants_since_phase_II(rabbitmq));
            unpack_conditions_from_spec(spec, invariants_since_phase_III(rabbitmq), true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(invariants_since_phase_III(rabbitmq)), invariants_since_phase_III(rabbitmq));

            helper_invariants::lemma_true_leads_to_always_create_server_cm_req_msg_in_flight_implies_at_after_create_server_cm_step(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_every_update_server_cm_req_does_the_same(spec, rabbitmq);
            helper_invariants::lemma_true_leads_to_always_every_create_server_cm_req_does_the_same(spec, rabbitmq);
            helper_invariants::lemma_true_leads_to_always_create_sts_req_msg_in_flight_implies_at_after_create_sts_step(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_update_sts_req_msg_in_flight_implies_at_after_update_sts_step(spec, rabbitmq.object_ref());
            helper_invariants::lemma_true_leads_to_always_every_update_sts_req_does_the_same(spec, rabbitmq);
            helper_invariants::lemma_true_leads_to_always_every_create_sts_req_does_the_same(spec, rabbitmq);

            leads_to_always_combine_n!(
                spec, true_pred(),
                lift_state(helper_invariants::create_server_cm_req_msg_in_flight_implies_at_after_create_server_cm_step(rabbitmq.object_ref())),
                lift_state(helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())),
                lift_state(helper_invariants::every_update_server_cm_req_does_the_same(rabbitmq)),
                lift_state(helper_invariants::every_create_server_cm_req_does_the_same(rabbitmq)),
                lift_state(helper_invariants::create_sts_req_msg_in_flight_implies_at_after_create_sts_step(rabbitmq.object_ref())),
                lift_state(helper_invariants::update_sts_req_msg_in_flight_implies_at_after_update_sts_step(rabbitmq.object_ref())),
                lift_state(helper_invariants::every_update_sts_req_does_the_same(rabbitmq)),
                lift_state(helper_invariants::every_create_sts_req_does_the_same(rabbitmq))
            );

            leads_to_trans_temp(spec, true_pred(), invariants_since_phase_III(rabbitmq), always(current_state_matches(rabbitmq)));
        }
    );
    assert_by(
        invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq)).entails(
            true_pred().leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq).and(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))).and(invariants_since_phase_I(rabbitmq));
            unpack_conditions_from_spec(spec, invariants_since_phase_II(rabbitmq), true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(invariants_since_phase_II(rabbitmq)), invariants_since_phase_II(rabbitmq));

            terminate::reconcile_eventually_terminates(spec, rabbitmq);
            RMQCluster::lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, rabbitmq);
            leads_to_trans_temp(spec, true_pred(), invariants_since_phase_II(rabbitmq), always(current_state_matches(rabbitmq)));
        }
    );

    // Now we eliminate the assumption []RMQCluster::crash_disabled() /\ []busy_disabled.

    // Then we unpack the assumption of []RMQCluster::desired_state_is(rabbitmq) from spec.
    assert_by(
        invariants(rabbitmq)
        .entails(
            always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(current_state_matches(rabbitmq)))
        ),
        {
            let spec = invariants(rabbitmq);
            let assumption = always(lift_state(RMQCluster::desired_state_is(rabbitmq)));
            unpack_conditions_from_spec(spec, assumption, true_pred(), always(current_state_matches(rabbitmq)));
            temp_pred_equality(true_pred().and(assumption), assumption);
        }
    );

    entails_trans(
        cluster_spec().and(derived_invariants_since_beginning(rabbitmq)), invariants(rabbitmq),
        always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(current_state_matches(rabbitmq)))
    );
    sm_spec_entails_all_invariants(rabbitmq);
    simplify_predicate(cluster_spec(), derived_invariants_since_beginning(rabbitmq));
}

}
