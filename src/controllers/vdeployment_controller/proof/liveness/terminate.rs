use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::reconciler::spec::io::*;
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*, util::*},
    proof::predicate::*,
};
use crate::vreplicaset_controller::trusted::spec_types::VReplicaSetView;
// make encoding steps easier
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use vstd::prelude::*;

verus! {

// serve as trigger to make Verus happy
pub open spec fn scale_down_old_vrs_rank_n(n: nat) -> spec_fn(ReconcileLocalState) -> bool {
    at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(n)), Error]
}

pub open spec fn new_vrs_some_and_replicas(n: nat) -> spec_fn(VDeploymentReconcileState) -> bool {
    // vrs.spec.replicas.is_None => 1 replica
    |vds: VDeploymentReconcileState| vds.new_vrs is Some && vds.new_vrs.unwrap().spec.replicas.unwrap_or(1) == n
}

pub proof fn reconcile_eventually_terminates(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
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
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)))),
        spec.entails(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref()))))),
        // no request in init
        spec.entails(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![Init]))))),
        spec.entails(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterEnsureNewVRS]))))),
        // there is always pending request for vd to proceed
        spec.entails(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterListVRS]))))),
        spec.entails(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterCreateNewVRS]))))),
        spec.entails(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleNewVRS]))))),
        spec.entails(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleDownOldVRS]))))),
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
        
        // Unwrap tla_foralls for all relevant preconditions for VDeploymentView.
        assert forall |vd: VDeploymentView| #![auto]
        spec.entails(always(
            lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref()))
        )) by {
            always_tla_forall_apply::<ClusterState, VDeploymentView>(
            spec,
            |vd: VDeploymentView|
            lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())),
            vd
            );
        }

        assert forall |vd: VDeploymentView| #![auto]
        spec.entails(always(
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_or![Init]
        )))) by {
            always_tla_forall_apply::<ClusterState, VDeploymentView>(
            spec,
            |vd: VDeploymentView|
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                controller_id,
                vd.object_ref(),
                at_step_or![Init]
            )),
            vd
            );
        }

        assert forall |vd: VDeploymentView| #![auto]
        spec.entails(always(
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_or![AfterEnsureNewVRS]
        )))) by {
            always_tla_forall_apply::<ClusterState, VDeploymentView>(
            spec,
            |vd: VDeploymentView|
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                controller_id,
                vd.object_ref(),
                at_step_or![AfterEnsureNewVRS]
            )),
            vd
            );
        }

        assert forall |vd: VDeploymentView| #![auto]
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_or![AfterListVRS]
        )))) by {
            always_tla_forall_apply::<ClusterState, VDeploymentView>(
            spec,
            |vd: VDeploymentView|
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vd.object_ref(),
                at_step_or![AfterListVRS]
            )),
            vd
            );
        }

        assert forall |vd: VDeploymentView| #![auto]
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_or![AfterCreateNewVRS]
        )))) by {
            always_tla_forall_apply::<ClusterState, VDeploymentView>(
            spec,
            |vd: VDeploymentView|
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vd.object_ref(),
                at_step_or![AfterCreateNewVRS]
            )),
            vd
            );
        }

        assert forall |vd: VDeploymentView| #![auto]
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_or![AfterScaleNewVRS]
        )))) by {
            always_tla_forall_apply::<ClusterState, VDeploymentView>(
            spec,
            |vd: VDeploymentView|
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vd.object_ref(),
                at_step_or![AfterScaleNewVRS]
            )),
            vd
            );
        }

        assert forall |vd: VDeploymentView| #![auto]
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_or![AfterScaleDownOldVRS]
        )))) by {
            always_tla_forall_apply::<ClusterState, VDeploymentView>(
            spec,
            |vd: VDeploymentView|
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vd.object_ref(),
                at_step_or![AfterScaleDownOldVRS]
            )),
            vd
            );
        }
        // End unwrapping foralls.
        if key.kind == VDeploymentView::kind() {
            let vd = make_vd(); // havoc for VDeploymentView
            let vd_with_key = VDeploymentView {
            metadata: ObjectMetaView {
                name: Some(key.name),
                namespace: Some(key.namespace),
                ..vd.metadata
            },
            ..vd
            };
            assert(key == vd_with_key.object_ref());

            reconcile_eventually_terminates_on_vd_object(
            spec, vd_with_key, cluster, controller_id
            );
        } else {
            always_weaken(
                spec, 
                lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id)),
                lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))
            );

            let terminated_vd = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key);
            assert forall |ex|
            spec.entails(always(lift_state(terminated_vd)))
            implies 
                #[trigger] spec.implies(always(
                true_pred().and(true_pred()).and(true_pred())
                .implies(later(lift_state(terminated_vd)))
                )).satisfied_by(ex) by {
            if spec.satisfied_by(ex) {
                assert forall |n: nat| 
                spec.satisfied_by(ex)
                && spec.entails(always(lift_state(terminated_vd)))
                implies 
                    #[trigger] true_pred().and(true_pred()).and(true_pred())
                    .implies(later(lift_state(terminated_vd))).satisfied_by(ex.suffix(n)) by {
                    assert(valid(spec.implies(always(lift_state(terminated_vd)))));
                    assert(spec.implies(always(lift_state(terminated_vd))).satisfied_by(ex));
                    assert(always(lift_state(terminated_vd)).satisfied_by(ex));
                    assert(lift_state(terminated_vd).satisfied_by(ex.suffix(n + 1)));
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

uninterp spec fn make_vd() -> VDeploymentView;

pub proof fn reconcile_eventually_terminates_on_vd_object(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
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
    spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()))),
    spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)))),
    spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())))),
    // no request in init
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![Init])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterEnsureNewVRS])))),
    // there is always pending request for vd to proceed
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterListVRS])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterCreateNewVRS])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleNewVRS])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleDownOldVRS])))),
ensures
    spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())))),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref());
    let reconcile_done = cluster.reconciler_reconcile_done(controller_id, vd.object_ref());
    let reconcile_error = cluster.reconciler_reconcile_error(controller_id, vd.object_ref());
    // 1, prove that reconcile_done \/ reconcile_error \/ reconcile_idle ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, vd.object_ref());
    cluster.lemma_reconcile_done_leads_to_reconcile_idle(spec, controller_id, vd.object_ref());
    temp_pred_equality(lift_state(lift_local(controller_id, vd, at_step_or![Error])), lift_state(reconcile_error));
    temp_pred_equality(lift_state(lift_local(controller_id, vd, at_step_or![Done])), lift_state(reconcile_done));
    entails_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));
    // 2, AfterScaleDownOldVRS ~> reconcile_idle.
    // 2.1, AfterScaleDownOldVRS && state.old_vrs_index == 0 ~> reconcile_idle.
    // Done ~> idle && Error ~> idle => Done \/ Error ~> idle
    or_leads_to_combine_and_equality!(spec,
        lift_state(lift_local(controller_id, vd, at_step_or![Error, Done])),
        lift_state(reconcile_error),
        lift_state(reconcile_done);
        lift_state(reconcile_idle)
    );
    let zero = 0 as nat;
    // AfterScaleDownOldVRS && state.old_vrs_index == 0 ~> Done \/ Error ~> idle
    lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
        spec, vd, controller_id, AfterScaleDownOldVRS, old_vrs_list_len(zero)
    );
    // 0 ~> Done | Error ~> idle
    assert(forall |input_cr, resp_o, s| #![trigger dummy((input_cr, resp_o, s))] at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(zero))](s)
        ==> at_step_or![Error, Done]((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0));
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, controller_id, vd.marshal(),
        at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(zero))],
        at_step_or![Error, Done]
    );
    // 0 | Error ~> idle
    or_leads_to_combine_and_equality!(
        spec, lift_state(lift_local(controller_id, vd, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(zero)), Error])),
        lift_state(lift_local(controller_id, vd, at_step_or![Error])),
        lift_state(lift_local(controller_id, vd, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(zero))]));
        lift_state(reconcile_idle)
    );
    // 2.2 AfterScaleDownOldVRS && n ~> 0 | Error ~> idle
    // hack to make Verus happy with trigger on macro
    let scale_down_old_vrs_rank_n = |n: nat| at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(n)), Error];
    assert forall |n: nat|
        spec.entails(lift_state(#[trigger] lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n)))
                     .leads_to(lift_state(lift_local(controller_id, vd, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(zero)), Error])))) by {
        // n | Error ~> n - 1 | Error
        assert forall |n: nat|
            n > 0 implies spec.entails(lift_state(lift_local(controller_id, vd, #[trigger] scale_down_old_vrs_rank_n(n)))
                                       .leads_to(lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n((n - 1) as nat))))) by {
            // Error ~> n - 1
            entails_implies_leads_to(spec,
                lift_state(lift_local(controller_id, vd, at_step_or![Error])),
                lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n((n - 1) as nat)))
            );
            // n ~> n - 1
            lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
                spec, vd, controller_id, AfterScaleDownOldVRS, old_vrs_list_len(n)
            );
            cluster.lemma_from_some_state_to_arbitrary_next_state(
                spec, controller_id, vd.marshal(),
                at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(n))],
                scale_down_old_vrs_rank_n((n - 1) as nat)
            );
            or_leads_to_combine_and_equality!(spec,
                lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n))),
                lift_state(lift_local(controller_id, vd, at_step_or![Error])),
                lift_state(lift_local(controller_id, vd, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(n))]));
                lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n((n - 1) as nat)))
            );
        }
        // n | Error ~> n - 1 | Error ~> 0 | Error
        leads_to_rank_step_one(spec, |n| lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n))));
        // n | Error ~> 0 | Error
        // TODO: investigate why we need |n|f(n) instead of f, could be a bug in verus
        assert(spec.entails((|n| lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n))))(n)
                            .leads_to((|n| lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n))))(0))));
        // (n | Error() ~> (0 | Error) ~> reconcile_idle
        leads_to_trans_n!(spec,
            lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n))),
            lift_state(lift_local(controller_id, vd, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(zero)), Error])),
            lift_state(reconcile_idle)
        );
    }
    // \A n | Error |= \E n | Error
    leads_to_exists_intro(spec,
        |n| lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n))),
        lift_state(lift_local(controller_id, vd, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(zero)), Error]))
    );
    // \E n | Error ~> idle
    leads_to_trans_n!(spec,
        tla_exists(|n| lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n)))),
        lift_state(lift_local(controller_id, vd, at_step_or![(AfterScaleDownOldVRS, old_vrs_list_len(zero)), Error])),
        lift_state(reconcile_idle)
    );
    // 2.3 AfterScaleDownOldVRS ~> AfterScaleDownOldVRS && \E n | Error ~> idle
    assert(spec.entails(lift_state(lift_local(controller_id, vd, at_step_or![AfterScaleDownOldVRS])).leads_to(lift_state(reconcile_idle)))) by {
        // p |= p(n)
        // hack to make Verus happy with trigger on macro
        let p = lift_state(lift_local(controller_id, vd, at_step_or![AfterScaleDownOldVRS]));
        assert forall |ex| #[trigger] p.satisfied_by(ex)
            implies tla_exists(|n| lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n))))
                    .satisfied_by(ex) by {
                let s_marshalled = ex.head().ongoing_reconciles(controller_id)[vd.object_ref()].local_state;
                let witness_n = VDeploymentReconcileState::unmarshal(s_marshalled).unwrap().old_vrs_index;
                assert((|n| lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n))))(witness_n).satisfied_by(ex));
            }
        assert(spec.entails(p.leads_to(lift_state(reconcile_idle)))) by {
            // p ~> p(n)
            entails_implies_leads_to(spec, p,
                tla_exists(|n| lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n)))));
            // p ~> p(n) ~> idle
            leads_to_trans_n!(spec,
                p,
                tla_exists(|n| lift_state(lift_local(controller_id, vd, scale_down_old_vrs_rank_n(n)))),
                lift_state(reconcile_idle)
            );
        }
    }
    // 3, AfterEnsureNewVRS ~> idle.
    or_leads_to_combine_and_equality!(spec,
        lift_state(lift_local(controller_id, vd, at_step_or![AfterScaleDownOldVRS, Error, Done])),
        lift_state(lift_local(controller_id, vd, at_step_or![AfterScaleDownOldVRS])),
        lift_state(lift_local(controller_id, vd, at_step_or![Error])),
        lift_state(lift_local(controller_id, vd, at_step_or![Done]));
        lift_state(reconcile_idle)
    );
    assert(forall |input_cr, resp_o, s| #![trigger dummy((input_cr, resp_o, s))]
        at_step_or![AfterEnsureNewVRS](s) ==> at_step_or![AfterScaleDownOldVRS, Error, Done]
                                             ((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0));
    // AfterEnsureNewVRS is similar to init on no pending req/resp is needed for the transition to next step
    // let me borrow this lemma for init here
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vd.marshal(),
        at_step_or![AfterEnsureNewVRS],
        at_step_or![AfterScaleDownOldVRS, Error, Done]
    );
    // 4, AfterScaleNewVRS ~> idle.
    or_leads_to_combine_and_equality!(spec,
        lift_state(lift_local(controller_id, vd, at_step_or![AfterEnsureNewVRS, Error])),
        lift_state(lift_local(controller_id, vd, at_step_or![AfterEnsureNewVRS])),
        lift_state(lift_local(controller_id, vd, at_step_or![Error]));
        lift_state(reconcile_idle)
    );
    assert(forall |input_cr, resp_o, s| #![trigger dummy((input_cr, resp_o, s))] 
        at_step_or![AfterScaleNewVRS](s) ==> at_step_or![AfterEnsureNewVRS, Error]
                                             ((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0));
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, controller_id, vd.marshal(),
        at_step_or![AfterScaleNewVRS],
        at_step_or![AfterEnsureNewVRS, Error]
    );
    // 5, AfterCreateNewVRS ~> idle
    assert(forall |input_cr, resp_o, s| #![trigger dummy((input_cr, resp_o, s))]
        at_step_or![AfterCreateNewVRS](s) ==> at_step_or![AfterEnsureNewVRS, Error]
                                              ((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0));
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, controller_id, vd.marshal(),
        at_step_or![AfterCreateNewVRS],
        at_step_or![AfterEnsureNewVRS, Error]
    );
    // 6, AfterListVRS ~> idle
    or_leads_to_combine_and_equality!(spec,
        lift_state(lift_local(controller_id, vd, at_step_or![AfterCreateNewVRS, AfterScaleNewVRS, AfterEnsureNewVRS, Error])),
        lift_state(lift_local(controller_id, vd, at_step_or![AfterCreateNewVRS])),
        lift_state(lift_local(controller_id, vd, at_step_or![AfterScaleNewVRS])),
        lift_state(lift_local(controller_id, vd, at_step_or![AfterEnsureNewVRS, Error]));
        lift_state(reconcile_idle)
    );
    assert(forall |input_cr, resp_o, s| #![trigger dummy((input_cr, resp_o, s))]
        at_step_or![AfterListVRS](s) ==> at_step_or![AfterCreateNewVRS, AfterScaleNewVRS, AfterEnsureNewVRS, Error]
                                         ((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0));
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, controller_id, vd.marshal(),
        at_step_or![AfterListVRS],
        at_step_or![AfterCreateNewVRS, AfterScaleNewVRS, AfterEnsureNewVRS, Error]
    );
    // 7, Init ~> idle
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vd.marshal(),
        at_step_or![Init],
        at_step_or![AfterListVRS]
    );
    // Finally, True ~> idle
    let bundle = lift_state(lift_local(controller_id, vd, at_step_or![Init]))
        .or(lift_state(lift_local(controller_id, vd, at_step_or![AfterListVRS])))
        .or(lift_state(lift_local(controller_id, vd, at_step_or![AfterCreateNewVRS])))
        .or(lift_state(lift_local(controller_id, vd, at_step_or![AfterScaleNewVRS])))
        .or(lift_state(lift_local(controller_id, vd, at_step_or![AfterEnsureNewVRS])))
        .or(lift_state(lift_local(controller_id, vd, at_step_or![AfterScaleDownOldVRS])))
        .or(lift_state(lift_local(controller_id, vd, at_step_or![Done])))
        .or(lift_state(lift_local(controller_id, vd, at_step_or![Error])))
        .or(lift_state(reconcile_idle));
    assert(forall |ex| true_pred::<ClusterState>().satisfied_by(ex) ==> bundle.satisfied_by(ex));
    temp_pred_equality(bundle, true_pred::<ClusterState>());
    or_leads_to_combine_and_equality!(spec,
        true_pred::<ClusterState>(),
        lift_state(reconcile_idle),
        lift_state(lift_local(controller_id, vd, at_step_or![Init])),
        lift_state(lift_local(controller_id, vd, at_step_or![AfterListVRS])),
        lift_state(lift_local(controller_id, vd, at_step_or![AfterCreateNewVRS])),
        lift_state(lift_local(controller_id, vd, at_step_or![AfterScaleNewVRS])),
        lift_state(lift_local(controller_id, vd, at_step_or![AfterEnsureNewVRS])),
        lift_state(lift_local(controller_id, vd, at_step_or![AfterScaleDownOldVRS])),
        lift_state(lift_local(controller_id, vd, at_step_or![Done])),
        lift_state(lift_local(controller_id, vd, at_step_or![Error]));
        lift_state(reconcile_idle)
    );
}

// what is satisfied at step should also be satisfied at step and pred
pub proof fn lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
    spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int,
    step: VDeploymentReconcileStepView, pred: spec_fn(VDeploymentReconcileState) -> bool
)
requires
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, vd.object_ref(), at_step_or![step]
    )))),
ensures
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, vd.object_ref(), at_step_or![(step, pred)]
    )))),
{
    let pre = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, vd.object_ref(), at_step_or![step]
    ));
    let post = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, vd.object_ref(), at_step_or![(step, pred)]
    ));
    assert forall |ex| #![auto] spec.satisfied_by(ex) && spec.entails(always(pre)) implies always(post).satisfied_by(ex) by {
        assert(forall |ex| #[trigger] spec.implies(always(pre)).satisfied_by(ex));
        assert(forall |ex| spec.implies(always(pre)).satisfied_by(ex) <==> (spec.satisfied_by(ex) ==> #[trigger] always(pre).satisfied_by(ex)));
        assert(always(pre).satisfied_by(ex));
        assert(forall |i: nat| #![auto] pre.satisfied_by(ex.suffix(i)) ==> post.satisfied_by(ex.suffix(i)));
    }
}
}