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
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
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
        spec.entails(tla_forall(|vrs: VReplicaSetView| 
            true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))
        )),
{
    let pre = {
        &&& spec.entails(always(lift_action(cluster.next())))
        &&& cluster.type_is_installed_in_cluster::<VReplicaSetView>()
        &&& cluster.controller_models.contains_pair(controller_id, vrs_controller_model())
        &&& spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))))
        &&& spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i)))
        &&& spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i)))
        &&& spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i))))
        &&& spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
        &&& spec.entails(always(lift_state(Cluster::crash_disabled(controller_id))))
        &&& spec.entails(always(lift_state(Cluster::req_drop_disabled())))
        &&& spec.entails(always(lift_state(Cluster::pod_monkey_disabled())))
        &&& spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id())))
        &&& spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
        &&& spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
        &&& spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>())))
        &&& spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id))))
        &&& spec.entails(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))))
        &&& spec.entails(always(tla_forall(|vrs: VReplicaSetView| 
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::Init)
            )))))
        &&& spec.entails(always(tla_forall(|vrs: VReplicaSetView| 
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::AfterListPods)
            )))))
        &&& spec.entails(always(tla_forall(|vrs: VReplicaSetView| 
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
                )
            )))))
        &&& spec.entails(always(tla_forall(|vrs: VReplicaSetView| 
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
                )
            )))))
    };

    assert forall |vrs: VReplicaSetView| #![trigger vrs.object_ref()] pre implies 
        spec.entails(true_pred().leads_to(
            lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()))
        )) by {
        
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

        reconcile_eventually_terminates_on_vrs_object(
            spec, vrs, cluster, controller_id
        );
    }

    spec_entails_tla_forall(
        spec,
        |vrs: VReplicaSetView| 
        true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))
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
    assume(false);
    
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

#[verifier(external_body)]
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
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
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
{}

#[verifier(external_body)]
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
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
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
{}

#[verifier(external_body)]
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
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
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
{}

// #[verifier(external_body)]
// pub proof fn lemma_from_after_list_pods_to_reconcile_idle(
//     spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
// )
//     requires
//         spec.entails(always(lift_action(cluster.next()))),
//         cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
//         cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
//         spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
//         spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
//         spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
//         spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
//         spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
//         spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
//         spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
//         spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
//         spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
//         spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
//         spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
//         spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
//         spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
//         spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
//         // Make sure there is a message in flight, so we can progress to the next state.
//         spec.entails(always(
//             lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
//                 controller_id,
//                 vrs.object_ref(),
//                 at_step_closure(VReplicaSetRecStepView::AfterListPods)
//             )))),

//     ensures
//         spec.entails(true_pred().leads_to(
//             lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()))
//         )),

}
