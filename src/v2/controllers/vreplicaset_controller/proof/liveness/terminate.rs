// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
    proof::{helper_invariants, helper_lemmas, liveness::{api_actions::*}, predicate::*},
};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VReplicaSetView>(controller_id)))),
        spec.entails(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref()))))),
        spec.entails(always(tla_forall(|vrs: VReplicaSetView| 
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::Init)
            ))))),
        spec.entails(always(tla_forall(|vrs: VReplicaSetView| 
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::AfterListPods)
            ))))),
        spec.entails(always(tla_forall(|vrs: VReplicaSetView| 
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
                )
            ))))),
        spec.entails(always(tla_forall(|vrs: VReplicaSetView| 
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
                )
            ))))),
    ensures
        spec.entails(tla_forall(|key: ObjectRef| 
            true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)))
        )),
{
    let post = |key: ObjectRef|
        true_pred().leads_to(lift_state(
            |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)
        ));

    assert forall |key: ObjectRef| spec.entails(#[trigger] post(key)) by {
        
        // Unwrap tla_foralls for all relevant preconditions.
        assert forall |vrs: VReplicaSetView| #![auto]
        spec.entails(always(
            lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref()))
        )) by {
            always_tla_forall_apply::<ClusterState, VReplicaSetView>(
                spec,
                |vrs: VReplicaSetView| 
                lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
                vrs
            );
        }

        assert forall |vrs: VReplicaSetView| #![auto]
        spec.entails(always(
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::Init)
        )))) by {
            always_tla_forall_apply::<ClusterState, VReplicaSetView>(
                spec,
                |vrs: VReplicaSetView| 
                lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                    controller_id,
                    vrs.object_ref(),
                    at_step_closure(VReplicaSetRecStepView::Init)
                )),
                vrs
            );
        }

        assert forall |vrs: VReplicaSetView| #![auto]
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::AfterListPods)
        )))) by {
            always_tla_forall_apply::<ClusterState, VReplicaSetView>(
                spec,
                |vrs: VReplicaSetView| 
                lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                    controller_id,
                    vrs.object_ref(),
                    at_step_closure(VReplicaSetRecStepView::AfterListPods)
                )),
                vrs
            );
        }

        assert forall |vrs: VReplicaSetView| #![auto]
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
                )
        )))) by {
            always_tla_forall_apply::<ClusterState, VReplicaSetView>(
                spec,
                |vrs: VReplicaSetView| 
                lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                    controller_id,
                    vrs.object_ref(),
                    unwrap_local_state_closure(
                        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
                    )
                )),
                vrs
            );
        }

        assert forall |vrs: VReplicaSetView| #![auto]
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
                )
        )))) by {
            always_tla_forall_apply::<ClusterState, VReplicaSetView>(
                spec,
                |vrs: VReplicaSetView| 
                lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                    controller_id,
                    vrs.object_ref(),
                    unwrap_local_state_closure(
                        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
                    )
                )),
                vrs
            );
        }
        // End unwrapping foralls.

        if key.kind == VReplicaSetView::kind() {
            let vrs = make_vrs(); // havoc for VReplicaSetView
            let vrs_with_key = VReplicaSetView {
                metadata: ObjectMetaView {
                    name: Some(key.name),
                    namespace: Some(key.namespace),
                    ..vrs.metadata
                },
                ..vrs
            };
            assert(key == vrs_with_key.object_ref());
            
            reconcile_eventually_terminates_on_vrs_object(
                spec, vrs_with_key, cluster, controller_id
            );
        } else {
            always_weaken(
                spec, 
                lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VReplicaSetView>(controller_id)),
                lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))
            );


            let terminated_vrs = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key);
            assert forall |ex|
                spec.entails(always(lift_state(terminated_vrs)))
                implies 
                    #[trigger] spec.implies(always(
                        true_pred().and(true_pred()).and(true_pred())
                        .implies(later(lift_state(terminated_vrs)))
                    )).satisfied_by(ex) by {
                if spec.satisfied_by(ex) {
                    assert forall |n: nat| 
                        spec.satisfied_by(ex)
                        && spec.entails(always(lift_state(terminated_vrs)))
                        implies 
                            #[trigger] true_pred().and(true_pred()).and(true_pred())
                            .implies(later(lift_state(terminated_vrs))).satisfied_by(ex.suffix(n)) by {
                        assert(valid(spec.implies(always(lift_state(terminated_vrs)))));
                        assert(spec.implies(always(lift_state(terminated_vrs))).satisfied_by(ex));
                        assert(always(lift_state(terminated_vrs)).satisfied_by(ex));
                        assert(lift_state(terminated_vrs).satisfied_by(ex.suffix(n + 1)));
                    }
                }
            }

            entails_implies_leads_to(spec, always(true_pred()), true_pred());
            wf1_variant_temp(
                spec,
                true_pred(),
                true_pred(),
                true_pred(),
                lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)),
            );
        }
    }

    spec_entails_tla_forall(
        spec,
        post
    );
}

pub proof fn reconcile_eventually_terminates_on_vrs_object(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        spec.entails(always(
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::Init)
            )))),
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::AfterListPods)
            )))),
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
                )
            )))),
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
                )
            )))),
    ensures
        spec.entails(true_pred().leads_to(
            lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()))
        )),
{
    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref());
    
    // First, prove that reconcile_done \/ reconcile_error \/ reconcile_ide ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, vrs.object_ref());
    cluster.lemma_reconcile_done_leads_to_reconcile_idle(spec, controller_id, vrs.object_ref());
    temp_pred_equality(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done)), lift_state(cluster.reconciler_reconcile_done(controller_id, vrs.object_ref())));
    temp_pred_equality(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)), lift_state(cluster.reconciler_reconcile_error(controller_id, vrs.object_ref())));
    entails_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));

    // Second, prove that after_create_pod_rank(0) \/ after_delete_pod_rank(0) ~> reconcile_idle.
    lemma_from_after_create_or_delete_pod_rank_zero_to_reconcile_idle(spec, vrs, cluster, controller_id);

    // Third, prove for all n that AfterCreatePod(n) ~> reconcile_idle.
    assert forall |n: nat| #![auto]
        spec.entails(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n)))
                    .leads_to(lift_state(reconcile_idle))) by {
        assert forall |n: nat| #![trigger after_create_pod_rank(controller_id, vrs, n)]
                    n > 0 implies spec.entails(lift_state(after_create_pod_rank(controller_id, vrs, n))
                                    .leads_to(lift_state(after_create_pod_rank(controller_id, vrs, (n - 1) as nat)))) by {
            lemma_from_after_create_pod_rank_n_to_create_pod_rank_n_minus_1(spec, vrs, cluster, controller_id, n);
        }
        leads_to_rank_step_one(spec, |n| lift_state(after_create_pod_rank(controller_id, vrs, n)));

        always_implies_to_leads_to(
            spec,
            lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n))),
            lift_state(after_create_pod_rank(controller_id, vrs, n))
        );
        assert(spec.entails((|n| lift_state(after_create_pod_rank(controller_id, vrs, n)))(n)
                                .leads_to((|n| lift_state(after_create_pod_rank(controller_id, vrs, n)))(0))));
        leads_to_trans_n!(
            spec,
            lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n))),
            lift_state(after_create_pod_rank(controller_id, vrs, n)),
            lift_state(after_create_pod_rank(controller_id, vrs, 0)),
            lift_state(reconcile_idle)
        );
    }

    // Similarly prove for all n that AfterDeletePod(n) ~> reconcile_idle.
    assert forall |n: nat| #![auto]
        spec.entails(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n)))
                    .leads_to(lift_state(reconcile_idle))) by {
        assert forall |n: nat| #![trigger after_delete_pod_rank(controller_id, vrs, n)]
                    n > 0 implies spec.entails(lift_state(after_delete_pod_rank(controller_id, vrs, n))
                                    .leads_to(lift_state(after_delete_pod_rank(controller_id, vrs, (n - 1) as nat)))) by {
            lemma_from_after_delete_pod_rank_n_to_delete_pod_rank_n_minus_1(spec, vrs, cluster, controller_id, n);
        }
        leads_to_rank_step_one(spec, |n| lift_state(after_delete_pod_rank(controller_id, vrs, n)));

        always_implies_to_leads_to(
            spec,
            lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n))),
            lift_state(after_delete_pod_rank(controller_id, vrs, n))
        );
        assert(spec.entails((|n| lift_state(after_delete_pod_rank(controller_id, vrs, n)))(n)
                                .leads_to((|n| lift_state(after_delete_pod_rank(controller_id, vrs, n)))(0))));
        leads_to_trans_n!(
            spec,
            lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n))),
            lift_state(after_delete_pod_rank(controller_id, vrs, n)),
            lift_state(after_delete_pod_rank(controller_id, vrs, 0)),
            lift_state(reconcile_idle)
        );
    }

    // Fourth, prove that after_list_pods | done ~> reconcile_idle.
    lemma_from_after_list_pods_to_reconcile_idle(spec, vrs, cluster, controller_id);
    assert(spec.entails(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done))
        .leads_to(lift_state(reconcile_idle))));
    or_leads_to_combine_n!(
        spec,
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterListPods)),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done));
        lift_state(reconcile_idle)
    );
    temp_pred_equality(lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(),
        |rs: ReconcileLocalState| (at_step_closure(VReplicaSetRecStepView::AfterListPods)(rs) || at_step_closure(VReplicaSetRecStepView::Done)(rs)))),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterListPods)).or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done)))
    );
    assert(spec.entails(lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), 
        |rs: ReconcileLocalState| (at_step_closure(VReplicaSetRecStepView::AfterListPods)(rs) || at_step_closure(VReplicaSetRecStepView::Done)(rs))))
        .leads_to(lift_state(reconcile_idle))));

    // Need some extra statements in V2 to prove the lemma.
    VReplicaSetReconcileState::marshal_preserves_integrity();

    // Fifth, prove that reconcile init state can reach AfterListPods.
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vrs.marshal(), 
        at_step_closure(VReplicaSetRecStepView::Init), 
        |rs: ReconcileLocalState| (at_step_closure(VReplicaSetRecStepView::AfterListPods)(rs) || at_step_closure(VReplicaSetRecStepView::Done)(rs))
    );

    // Finally, combine all cases
    leads_to_exists_intro(
        spec,
        |n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n))),
        lift_state(reconcile_idle)
    );
    leads_to_exists_intro(
        spec,
        |n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n))),
        lift_state(reconcile_idle)
    );
    let at_after_create_pod = |n: nat| {
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n)))
    };
    let at_after_delete_pod = |n: nat| {
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n)))
    };

    lemma_true_equal_to_reconcile_idle_or_at_any_state(vrs, controller_id);

    // Needed to show Init ~> Done.
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Init)),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Init)))
    );
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Init)),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterListPods)),
        tla_exists(at_after_create_pod),
        tla_exists(at_after_delete_pod),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done)),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error));
        lift_state(reconcile_idle)
    );
}

pub open spec fn at_step_state_pred(controller_id: int, vrs: VReplicaSetView, step: VReplicaSetRecStepView) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(
        controller_id, vrs.object_ref(), 
        |s: ReconcileLocalState| {
            let unmarshalled_state = VReplicaSetReconcileState::unmarshal(s).unwrap();
            unmarshalled_state.reconcile_step == step
        }
    )
}

pub open spec fn after_create_pod_rank(controller_id: int, vrs: VReplicaSetView, diff: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        ||| at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(diff))(s)
        // There may have been an error as well.
        ||| at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)(s)
    }
}

pub open spec fn after_delete_pod_rank(controller_id: int, vrs: VReplicaSetView, diff: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        ||| at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(diff))(s)
        // There may have been an error as well.
        ||| at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)(s)
    }
}

pub proof fn lemma_from_after_create_or_delete_pod_rank_zero_to_reconcile_idle(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        // Makes sure there is a message in flight, so we can progress to the next state.
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
                )
            )))),
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
                )
            )))),
        // The next state will lead to reconcile_idle
        spec.entails(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
    ensures
        spec.entails(lift_state(after_create_pod_rank(controller_id, vrs, 0))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
        spec.entails(lift_state(after_delete_pod_rank(controller_id, vrs, 0))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
{
    VReplicaSetReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();

    let state_after_create_or_delete = |s_marshalled: ReconcileLocalState| {
        let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
        s.reconcile_step == VReplicaSetRecStepView::Done
        || s.reconcile_step == VReplicaSetRecStepView::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), state_after_create_or_delete)),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done)),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error));
        lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) })
    );

    lemma_from_pending_req_in_flight_or_resp_in_flight_at_all_create_to_create_n(
        spec, vrs, cluster, controller_id, 0
    );
    lemma_from_pending_req_in_flight_or_resp_in_flight_at_all_delete_to_delete_n(
        spec, vrs, cluster, controller_id, 0
    );

    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, vrs.marshal(), at_step_closure(VReplicaSetRecStepView::AfterCreatePod(0)), state_after_create_or_delete);
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, vrs.marshal(), at_step_closure(VReplicaSetRecStepView::AfterDeletePod(0)), state_after_create_or_delete);

    // this block soley to get this through verus.
    let zero: nat = 0;
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(zero))),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterCreatePod(zero))))
    );
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(zero))),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterDeletePod(zero))))
    );
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Error)))
    );

    or_leads_to_combine_and_equality!(
        spec, lift_state(after_create_pod_rank(controller_id, vrs, zero)),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(zero))),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error));
        lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) })
    );
    or_leads_to_combine_and_equality!(
        spec, lift_state(after_delete_pod_rank(controller_id, vrs, zero)),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(zero))),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error));
        lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) })
    );
}

pub proof fn lemma_from_after_create_pod_rank_n_to_create_pod_rank_n_minus_1(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, n: nat
)
    requires
        n > 0,
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
                )
            )))),
    ensures
        spec.entails(lift_state(after_create_pod_rank(controller_id, vrs, n))
            .leads_to(lift_state(after_create_pod_rank(controller_id, vrs, (n - 1) as nat)))),
{
    VReplicaSetReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();

    let state_after_create = |s_marshalled: ReconcileLocalState| {
        let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
        s.reconcile_step == VReplicaSetRecStepView::AfterCreatePod((n - 1) as nat)
        || s.reconcile_step == VReplicaSetRecStepView::Error
    };

    entails_implies_leads_to(
        spec,
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)),
        lift_state(after_create_pod_rank(controller_id, vrs, (n - 1) as nat))
    );

    lemma_from_pending_req_in_flight_or_resp_in_flight_at_all_create_to_create_n(
        spec, vrs, cluster, controller_id, n
    );

    cluster.lemma_from_some_state_to_arbitrary_next_state(spec, controller_id, vrs.marshal(), at_step_closure(VReplicaSetRecStepView::AfterCreatePod(n)), state_after_create);

    // this block soley to get this through verus.
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n))),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterCreatePod(n))))
    );
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Error)))
    );

    always_implies_to_leads_to(
        spec,
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), state_after_create)),
        lift_state(after_create_pod_rank(controller_id, vrs, (n - 1) as nat))
    );
    leads_to_trans_n!(
        spec,
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n))),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), state_after_create)),
        lift_state(after_create_pod_rank(controller_id, vrs, (n - 1) as nat))
    );
    or_leads_to_combine_and_equality!(
        spec, lift_state(after_create_pod_rank(controller_id, vrs, n)),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n))),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error));
        lift_state(after_create_pod_rank(controller_id, vrs, (n - 1) as nat))
    );
}

pub proof fn lemma_from_after_delete_pod_rank_n_to_delete_pod_rank_n_minus_1(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, n: nat
)
    requires
        n > 0,
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
                )
            )))),
    ensures
        spec.entails(lift_state(after_delete_pod_rank(controller_id, vrs, n))
            .leads_to(lift_state(after_delete_pod_rank(controller_id, vrs, (n - 1) as nat)))),
{
    VReplicaSetReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();

    let state_after_delete = |s_marshalled: ReconcileLocalState| {
        let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
        s.reconcile_step == VReplicaSetRecStepView::AfterDeletePod((n - 1) as nat)
        || s.reconcile_step == VReplicaSetRecStepView::Error
    };

    entails_implies_leads_to(
        spec,
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)),
        lift_state(after_delete_pod_rank(controller_id, vrs, (n - 1) as nat))
    );

    lemma_from_pending_req_in_flight_or_resp_in_flight_at_all_delete_to_delete_n(
        spec, vrs, cluster, controller_id, n
    );

    cluster.lemma_from_some_state_to_arbitrary_next_state(spec, controller_id, vrs.marshal(), at_step_closure(VReplicaSetRecStepView::AfterDeletePod(n)), state_after_delete);

    // this block soley to get this through verus.
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n))),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterDeletePod(n))))
    );
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Error)))
    );

    always_implies_to_leads_to(
        spec,
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), state_after_delete)),
        lift_state(after_delete_pod_rank(controller_id, vrs, (n - 1) as nat))
    );
    leads_to_trans_n!(
        spec,
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n))),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), state_after_delete)),
        lift_state(after_delete_pod_rank(controller_id, vrs, (n - 1) as nat))
    );
    or_leads_to_combine_and_equality!(
        spec, lift_state(after_delete_pod_rank(controller_id, vrs, n)),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n))),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error));
        lift_state(after_delete_pod_rank(controller_id, vrs, (n - 1) as nat))
    );
}

pub proof fn lemma_from_after_list_pods_to_reconcile_idle(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        // Make sure there is a message in flight, so we can progress to the next state.
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::AfterListPods)
            )))),
        // Once we get to "after create" or "after delete", we can reach reconcile_idle.
        forall |n: nat| #![auto]
            spec.entails(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n)))
                .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
        forall |n: nat| #![auto]
            spec.entails(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n)))
                .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
    ensures
        spec.entails(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterListPods))
            .leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
{
    VReplicaSetReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();

    let state_after_list_pods = |s_marshalled: ReconcileLocalState| {
        let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
        ||| exists |n: nat| s.reconcile_step == VReplicaSetRecStepView::AfterCreatePod(n)
        ||| exists |n: nat| s.reconcile_step == VReplicaSetRecStepView::AfterDeletePod(n)
        ||| s.reconcile_step == VReplicaSetRecStepView::Done
        ||| s.reconcile_step == VReplicaSetRecStepView::Error
    };
    leads_to_exists_intro(
        spec,
        |n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n))),
        lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()))
    );
    leads_to_exists_intro(
        spec,
        |n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n))),
        lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()))
    );
    let at_after_create_pod = |n: nat| {
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n)))
    };
    let at_after_delete_pod = |n: nat| {
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n)))
    };

    assert_by(
        tla_exists(at_after_create_pod) ==
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), |s_marshalled: ReconcileLocalState| {
            let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
            exists |n: nat| s.reconcile_step == VReplicaSetRecStepView::AfterCreatePod(n)
        })),
        {
            assert forall |ex| #![auto]
            lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), |s_marshalled: ReconcileLocalState| {
                let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
                exists |n: nat| s.reconcile_step == VReplicaSetRecStepView::AfterCreatePod(n)
            })).satisfied_by(ex) implies
            tla_exists(at_after_create_pod).satisfied_by(ex) by {
                let s_marshalled = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].local_state;
                let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
                let witness_n = choose |n: nat| s.reconcile_step == VReplicaSetRecStepView::AfterCreatePod(n);
                assert(at_after_create_pod(witness_n).satisfied_by(ex));
            }

            temp_pred_equality(
                tla_exists(at_after_create_pod),
                lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), |s_marshalled: ReconcileLocalState| {
                    let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
                    exists |n: nat| s.reconcile_step == VReplicaSetRecStepView::AfterCreatePod(n)
                }))
            );
        }
    );
    assert_by(
        tla_exists(at_after_delete_pod) ==
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), |s_marshalled: ReconcileLocalState| {
            let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
            exists |n: nat| s.reconcile_step == VReplicaSetRecStepView::AfterDeletePod(n)
        })),
        {
            assert forall |ex| #![auto]
            lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), |s_marshalled: ReconcileLocalState| {
                let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
                exists |n: nat| s.reconcile_step == VReplicaSetRecStepView::AfterDeletePod(n)
            })).satisfied_by(ex) implies
            tla_exists(at_after_delete_pod).satisfied_by(ex) by {
                let s_marshalled = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].local_state;
                let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
                let witness_n = choose |n: nat| s.reconcile_step == VReplicaSetRecStepView::AfterDeletePod(n);
                assert(at_after_delete_pod(witness_n).satisfied_by(ex));
            }

            temp_pred_equality(
                tla_exists(at_after_delete_pod),
                lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), |s_marshalled: ReconcileLocalState| {
                    let s = VReplicaSetReconcileState::unmarshal(s_marshalled).unwrap();
                    exists |n: nat| s.reconcile_step == VReplicaSetRecStepView::AfterDeletePod(n)
                }))
            );
        }
    );
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), state_after_list_pods)),
        tla_exists(at_after_create_pod),
        tla_exists(at_after_delete_pod),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done)),
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error));
        lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) })
    );

    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterListPods)),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterListPods)))
    );
    cluster.lemma_from_some_state_to_arbitrary_next_state(spec, controller_id, vrs.marshal(), at_step_closure(VReplicaSetRecStepView::AfterListPods), state_after_list_pods);

    leads_to_trans_n!(
        spec,
        lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterListPods)),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vrs.object_ref(), state_after_list_pods)),
        lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) })
    );
}

proof fn lemma_true_equal_to_reconcile_idle_or_at_any_state(vrs: VReplicaSetView, controller_id: int)
    ensures true_pred::<ClusterState>()
                == lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) })
                    .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Init)))
                    .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterListPods)))
                    .or(tla_exists(|n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n)))))
                    .or(tla_exists(|n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n)))))
                    .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done)))
                    .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)))
{
    let rhs = lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) })
        .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Init)))
        .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterListPods)))
        .or(tla_exists(|n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n)))))
        .or(tla_exists(|n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n)))))
        .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done)))
        .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)));
    
    assert forall |ex| #![auto] true_pred::<ClusterState>().satisfied_by(ex) implies rhs.satisfied_by(ex) by {
        let s = ex.head();
        if s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) {
            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
            let step = state.reconcile_step;
            match step {
                VReplicaSetRecStepView::AfterCreatePod(n) => {
                    // Introduce tla_exists with n as witness.
                    assert((|n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n))))(n).satisfied_by(ex));
                    assert(tla_exists(|n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n)))).satisfied_by(ex));
                },
                VReplicaSetRecStepView::AfterDeletePod(n) => {
                    // Introduce tla_exists with n as witness.
                    assert((|n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n))))(n).satisfied_by(ex));
                    assert(tla_exists(|n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n)))).satisfied_by(ex));
                },
                step => {},
            }
        }
    }

    temp_pred_equality(
        true_pred::<ClusterState>(),
        lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) })
            .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Init)))
            .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterListPods)))
            .or(tla_exists(|n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterCreatePod(n)))))
            .or(tla_exists(|n| lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::AfterDeletePod(n)))))
            .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Done)))
            .or(lift_state(at_step_state_pred(controller_id, vrs, VReplicaSetRecStepView::Error)))
    );
}

pub proof fn lemma_from_pending_req_in_flight_or_resp_in_flight_at_all_create_to_create_n(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, n: nat
)
    requires
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
                )
            )))),
    ensures
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::AfterCreatePod(n))
            )))),
{
    let pre = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id,
        vrs.object_ref(),
        unwrap_local_state_closure(
            |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
        )
    ));
    let post = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id,
        vrs.object_ref(),
        at_step_closure(VReplicaSetRecStepView::AfterCreatePod(n))
    ));

    assert forall |ex| #![auto] spec.satisfied_by(ex) && spec.entails(always(pre)) implies always(post).satisfied_by(ex) by {
        assert(forall |ex| #[trigger] spec.implies(always(pre)).satisfied_by(ex));
        assert(forall |ex| spec.implies(always(pre)).satisfied_by(ex) <==> (spec.satisfied_by(ex) ==> #[trigger] always(pre).satisfied_by(ex)));
        assert(always(pre).satisfied_by(ex));

        assert forall |i: nat| #![auto] pre.satisfied_by(ex.suffix(i)) implies post.satisfied_by(ex.suffix(i)) by {
        }
    }
}

pub proof fn lemma_from_pending_req_in_flight_or_resp_in_flight_at_all_delete_to_delete_n(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, n: nat
)
    requires
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
                )
            )))),
    ensures
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::AfterDeletePod(n))
            )))),
{
    let pre = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id,
        vrs.object_ref(),
        unwrap_local_state_closure(
            |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
        )
    ));
    let post = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id,
        vrs.object_ref(),
        at_step_closure(VReplicaSetRecStepView::AfterDeletePod(n))
    ));

    assert forall |ex| #![auto] spec.satisfied_by(ex) && spec.entails(always(pre)) implies always(post).satisfied_by(ex) by {
        assert(forall |ex| #[trigger] spec.implies(always(pre)).satisfied_by(ex));
        assert(forall |ex| spec.implies(always(pre)).satisfied_by(ex) <==> (spec.satisfied_by(ex) ==> #[trigger] always(pre).satisfied_by(ex)));
        assert(always(pre).satisfied_by(ex));

        assert forall |i: nat| #![auto] pre.satisfied_by(ex.suffix(i)) implies post.satisfied_by(ex.suffix(i)) by {
        }
    }
}

// Havoc function for VReplicaSetView.
spec fn make_vrs() -> VReplicaSetView;

}
