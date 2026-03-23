use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::*},
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::*, rely_guarantee::*},
    model::{install::*, reconciler::*},
    proof::{predicate::*, liveness::{api_actions::*, resource_match::*}, helper_lemmas::*, helper_invariants},
    proof::liveness::rolling_update::{predicate::*, composition::*, helper_lemmas::*}
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{seq_lib::*, set_lib::*};
use vstd::{seq_lib::*, map_lib::*, multiset::*};
use vstd::prelude::*;

verus !{

pub proof fn lemma_from_init_to_not_desired_state_is(vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, new_vrs: VReplicaSetView, diff: nat)
requires
    diff > 0,
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    spec.entails(tla_forall((|i| cluster.external_next().weak_fairness((controller_id, i))))),
    spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
ensures
    spec.entails(lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Init]),
        no_pending_req_in_cluster(vd, controller_id)
    )).and(
        always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff))
            .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref()))))
    ).leads_to(not(
        lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff))
    ))),
{
    let c = lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())));
    let inv = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id));
    let init = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Init]),
        no_pending_req_in_cluster(vd, controller_id)
    ));
    let list_req = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        pending_list_req_in_flight(vd, controller_id)
    ));
    assert(spec.entails(init.leads_to(list_req))) by {
        lemma_from_init_step_to_send_list_vrs_req(vd, spec, cluster, controller_id);
    }
    let list_req_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        req_msg_is_pending_list_req_in_flight(vd, controller_id, msg)
    ));
    // list_req == \E |msg| list_req_msg(msg)
    assert(list_req == tla_exists(list_req_msg)) by {
        assert forall |ex| #[trigger] list_req.satisfied_by(ex) implies tla_exists(list_req_msg).satisfied_by(ex) by {
            let req_msg = ex.head().ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            assert((|msg| list_req_msg(msg))(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(list_req, tla_exists(list_req_msg));
    }
    let list_resp = lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        exists_pending_list_resp_in_flight_and_match_req(vd, controller_id)
    ));
    // \A |msg| (list_req_msg(msg) ~> list_resp)
    assert forall |req_msg: Message| #[trigger] spec.entails(list_req_msg(req_msg).leads_to(list_resp)) by {
        lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp(vd, spec, cluster, controller_id, req_msg);
    };
    // \A |msg| (list_req_msg(msg) ~> list_resp) |= (\E |msg| list_resp_msg(msg)) ~> list_resp
    leads_to_exists_intro(spec, list_req_msg, list_resp);
    let list_resp_msg = |msg| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg)
    ));
    // list_resp == \E |msg| list_resp_msg(msg)
    assert(list_resp == tla_exists(list_resp_msg)) by {
        // list_resp |= \E |msg| list_resp_msg(msg)
        assert forall |ex| #[trigger] list_resp.satisfied_by(ex) implies tla_exists(list_resp_msg).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
            let resp_msg = choose |resp_msg| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s)
            };
            assert((list_resp_msg)(resp_msg).satisfied_by(ex));
        }
        temp_pred_equality(list_resp, tla_exists(list_resp_msg));
    };
    // since here, the path diverges from the proof of ESR
    // because we have stronger cluster environment assumption
    leads_to_trans(spec,
        init,
        list_req,
        list_resp
    );
    let after_list_with_nv = |i: (Message, Uid, ObjectRef, int, Option<int>)| lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, i.0),
        new_vrs_and_no_old_vrs_from_resp_objs(vd, controller_id, i.0, (i.1, i.2, i.3, i.4), new_vrs.object_ref())
    ));
    let post = not(lift_state(desired_state_is_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff)));
    assert(spec.entails(init.and(always(c)).leads_to(tla_exists(after_list_with_nv)))) by {
        leads_to_with_always(spec, init, list_resp, c);
        tla_exists_and_equality(list_req_msg, always(c));
        assert forall |msg| #![trigger list_resp_msg(msg)] spec.entails(list_resp_msg(msg).and(always(c)).and(always(inv))
            .leads_to(tla_exists(|i: (Message, Uid, ObjectRef, int, Option<int>)| after_list_with_nv((i.0, i.1, i.2, i.3, i.4))))) by {
            assert forall |ex| list_resp_msg(msg).satisfied_by(ex) && always(c).satisfied_by(ex) && always(inv).satisfied_by(ex)
                implies tla_exists(|i: (Message, Uid, ObjectRef, int, Option<int>)| after_list_with_nv((i.0, i.1, i.2, i.3, i.4))).satisfied_by(ex) by {
                always_to_current(ex, c);
                always_to_current(ex, inv);
                let s = ex.head();
                let nv = inductive_current_state_matches_implies_filter_old_and_new_vrs_from_resp_objs(vd, cluster, controller_id, msg, new_vrs.object_ref(), s);
                assert((|i: (Message, Uid, ObjectRef, int, Option<int>)| new_vrs_and_no_old_vrs_from_resp_objs(vd, controller_id, i.0, (i.1, i.2, i.3, i.4), new_vrs.object_ref()))((msg, nv.0, nv.1, nv.2, nv.3))(s));
            }
            entails_implies_leads_to(spec,
                list_resp_msg(msg).and(always(c)).and(always(inv)),
                tla_exists(|i: (Message, Uid, ObjectRef, int, Option<int>)| after_list_with_nv((i.0, i.1, i.2, i.3, i.4)))
            );
            always_double_equality(inv);
            leads_to_by_borrowing_inv(spec,
                list_resp_msg(msg).and(always(c)),
                tla_exists(|i: (Message, Uid, ObjectRef, int, Option<int>)| after_list_with_nv((i.0, i.1, i.2, i.3, i.4))),
                always(inv)
            );
        }
    }
    assert forall |i: (Message, Uid, ObjectRef, int, Option<int>)| #![trigger after_list_with_nv(i)] spec.entails(after_list_with_nv(i).leads_to(post)) by {
        // prove AfterScaleNewVRS is always reached
        assume(false);
    }
    leads_to_exists_intro(spec, after_list_with_nv, post);
    leads_to_trans(spec, init.and(always(c)), tla_exists(after_list_with_nv), post);
}

#[verifier(external_body)]
pub proof fn lemma_from_after_receive_list_resp_to_after_scale_new_vrs_with_nv(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message, new_vrs: VReplicaSetView, diff: nat
)
requires
    diff > 0,
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself(controller_id))),
    spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg)
    )).and(always(lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff))
            .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())))))
    .leads_to(lift_state(and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id)
    )))),
{
    let c = lift_state(current_state_matches_vrs_with_replicas_diff_and_key(vd, new_vrs, new_vrs.object_ref(), diff))
        .and(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs.object_ref())));
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS]),
        resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg),
        ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS]),
        local_state_at_after_scale_vrs(vd, controller_id, new_vrs.object_ref())
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        &&& forall |vd: VDeploymentView| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& vd_rely_condition(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lifted_vd_reconcile_request_only_interferes_with_itself(controller_id),
        lifted_vd_rely_condition(cluster, controller_id),
        lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
    );
    let input = (Some(resp_msg), Some(vd.object_ref()));
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            // Step::APIServerStep(input) => {
            //     let msg = input->0;
            //     lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
            //         s, s_prime, vd, cluster, controller_id, msg, Some(nv_uid_key_replicas), n
            //     );
            //     lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
            //         s, s_prime, vd, cluster, controller_id, msg, Some(nv_uid_key_replicas.0)
            //     );
            //     let resp_objs = resp_msg.content.get_list_response().res.unwrap();
            //     let vrs_list = objects_to_vrs_list(resp_objs)->0;
            //     let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
            //     assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies {
            //         let key = vrs.object_ref();
            //         let etcd_obj = s_prime.resources()[key];
            //         let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
            //         &&& s_prime.resources().contains_key(key)
            //         &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
            //         &&& valid_owned_obj_key(vd, s_prime)(key)
            //         &&& etcd_vrs.metadata.without_resource_version() == vrs.metadata.without_resource_version()
            //         &&& etcd_vrs.spec == vrs.spec
            //     } by {
            //         lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
            //             s, s_prime, vd, cluster, controller_id, msg
            //         );
            //     }
            // },
            // Step::ControllerStep(input) => {
            //     if input.0 == controller_id && input.1 == Some(resp_msg) && input.2 == Some(vd.object_ref()) {
            //         VDeploymentReconcileState::marshal_preserves_integrity();
            //         VReplicaSetView::marshal_preserves_integrity();
            //         lemma_from_list_resp_to_next_state(s, s_prime, vd, cluster, controller_id, resp_msg, Some(nv_uid_key_replicas), n);
            //     }
            // },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        VDeploymentReconcileState::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}


pub proof fn lemma_from_list_resp_with_nv_status_matching_spec_to_next_state(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, resp_msg: Message, new_vrs_key: ObjectRef
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(vd.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s),
    ru_resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg, new_vrs_key)(s),
ensures
    at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS])(s_prime),
    local_state_at_after_scale_vrs(vd, controller_id, new_vrs_key)(s_prime),
    ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id)(s_prime),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();
    broadcast use group_seq_properties;
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let etcd_obj = s.resources()[new_vrs_key];
    assert(objects_to_vrs_list(resp_objs) is Some);
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = objects_to_vrs_list(resp_objs)->0.filter(|vrs| valid_owned_vrs(vrs, vd));
    let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
    let new_vrs_uid = Some(etcd_obj.metadata.uid->0);
    let valid_owned_vrs_filter = |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd);
    let managed_vrs_list = vrs_list.filter(valid_owned_vrs_filter);
    assert(new_vrs_or_none is Some);
    let new_vrs = new_vrs_or_none->0;
    assert forall |vrs| #[trigger] vrs_list.contains(vrs) implies vrs.metadata.uid is Some by {
        let i = choose |i: int| 0 <= i < vrs_list.len() && vrs_list[i] == vrs;
        VReplicaSetView::marshal_preserves_metadata();
        assert(resp_objs.contains(resp_objs[i])); // trigger
        assert(VReplicaSetView::unmarshal(resp_objs[i]) is Ok);
        assert(vrs_list[i] == VReplicaSetView::unmarshal(resp_objs[i])->Ok_0);
    }
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies vrs.metadata.uid is Some by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, valid_owned_vrs_filter);
    }
    let old_vrs_list_filter_with_new_vrs = |vrs: VReplicaSetView| {
        &&& new_vrs_or_none is None || vrs.metadata.uid != new_vrs.metadata.uid
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    let another_filter_used_in_esr = |vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    assert(old_vrs_list == managed_vrs_list.filter(old_vrs_list_filter_with_new_vrs));
    // because in reconciler we don't know all objects has uid, which is guaranteed by cluster env predicates
    // so the filter in reconciler didn't use uid->0
    assert(managed_vrs_list.filter(old_vrs_list_filter_with_new_vrs) == managed_vrs_list.filter(another_filter_used_in_esr)) by {
        assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies
            (old_vrs_list_filter_with_new_vrs(vrs) == another_filter_used_in_esr(vrs)) by {
            assert(vrs.metadata.uid is Some);
            assert(new_vrs_uid is Some);
            assert(new_vrs.metadata.uid == new_vrs_uid);
        }
        same_filter_implies_same_result(managed_vrs_list, old_vrs_list_filter_with_new_vrs, another_filter_used_in_esr);
    }
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies vrs_list.contains(vrs) && valid_owned_vrs(vrs, vd) by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, valid_owned_vrs_filter);
    }
    assert forall |vrs: VReplicaSetView| #[trigger] old_vrs_list.contains(vrs) implies
        vrs_list.contains(vrs) && valid_owned_vrs(vrs, vd) && s.resources().contains_key(vrs.object_ref()) by {
        seq_filter_is_a_subset_of_original_seq(managed_vrs_list, old_vrs_list_filter_with_new_vrs);
    }
    assert(managed_vrs_list.contains(new_vrs) && vrs_list.contains(new_vrs) && valid_owned_vrs(new_vrs, vd) && match_template_without_hash(vd.spec.template)(new_vrs)) by {
        assert(managed_vrs_list.contains(new_vrs) && match_template_without_hash(vd.spec.template)(new_vrs)) by { // trigger
            // unwrap filter_old_and_new_vrs
            let non_zero_replicas_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
            if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).len() > 0 {
                seq_filter_is_a_subset_of_original_seq(managed_vrs_list, match_template_without_hash(vd.spec.template));
                if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(non_zero_replicas_filter).len() > 0 {
                    assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(non_zero_replicas_filter).contains(new_vrs));
                    seq_filter_is_a_subset_of_original_seq(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)), non_zero_replicas_filter);
                }
                assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).contains(new_vrs));
            } else {
                assert(new_vrs_or_none is None);
                assert(false);
            }
        }
    };
    let map_key = |vrs: VReplicaSetView| vrs.object_ref();
    assert(old_vrs_list.map_values(map_key).no_duplicates()) by { // triggering_cr.well_formed()
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
        lemma_no_duplication_in_resp_objs_implies_no_duplication_in_down_stream(triggering_cr, resp_objs);
    }
    assert(old_vrs_list.map_values(map_key).to_set()
        == filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s))) by {
        lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, new_vrs_uid, s);
    }
    assert(old_vrs_list.len() == 0) by {
        old_vrs_list.map_values(map_key).unique_seq_to_set();
        assert(old_vrs_list.map_values(map_key).len() == old_vrs_list.len());
        assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s)).len() == 0);
    }

    let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    assert(vds_prime.old_vrs_list == old_vrs_list);
    assert(vds_prime.old_vrs_index == old_vrs_list.len());

    // prove local_state_is_coherent_with_etcd_valid_and_coherent(s_prime)
    assert forall |i| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_index
        implies managed_vrs_list.contains(vds_prime.old_vrs_list[i]) by {
        assert(old_vrs_list.contains(vds_prime.old_vrs_list[i])); // trigger
    }
}

// this is dedicated for inductivity proof, for rank decrease proof, use the stronger version above
// TODO: merge with lemma_from_list_resp_to_next_state?
pub proof fn lemma_from_list_resp_with_nv_to_next_state(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key_replicas_status: (Uid, ObjectRef, int, Option<int>), new_vrs_key: ObjectRef
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(vd.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s),
    resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg)(s),
    new_vrs_and_no_old_vrs_from_resp_objs(vd, controller_id, resp_msg, nv_uid_key_replicas_status, new_vrs_key)(s),
ensures
    if nv_uid_key_replicas_status.3 is Some && (nv_uid_key_replicas_status.3->0 == nv_uid_key_replicas_status.2) && nv_uid_key_replicas_status.2 != vd.spec.replicas.unwrap_or(int1!()) { // mismatch_replicas
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS])(s_prime)
        &&& local_state_at_after_scale_vrs(vd, controller_id, new_vrs_key)(s_prime)
        &&& ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id)(s_prime)
        &&& nv_uid_key_replicas_status.1 == new_vrs_key
    } else {
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS])(s_prime)
        &&& local_state_is(vd, controller_id, Some((nv_uid_key_replicas_status.0, nv_uid_key_replicas_status.1, nv_uid_key_replicas_status.2)), 0)(s_prime)
        &&& no_pending_req_in_cluster(vd, controller_id)(s_prime)
    },
    ({ // for additional requirements in inductive csm
        let local_state_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[new_vrs_key])->Ok_0;
        &&& local_state_prime.new_vrs is Some
        &&& etcd_vrs.spec.replicas.unwrap_or(1) > 0 ==> {
            &&& local_state_prime.new_vrs->0.object_ref() == new_vrs_key
            &&& local_state_prime.new_vrs->0.metadata.uid->0 == etcd_vrs.metadata.uid->0
        }
        &&& local_state_prime.new_vrs->0.object_ref() != new_vrs_key ==> {
            &&& local_state_prime.new_vrs->0.spec.replicas.unwrap_or(1) == 0
        }
    }),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();
    broadcast use group_seq_properties;
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    assert(objects_to_vrs_list(resp_objs) is Some);
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = objects_to_vrs_list(resp_objs)->0.filter(|vrs| valid_owned_vrs(vrs, vd));
    let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
    let new_vrs_uid = Some(nv_uid_key_replicas_status.0);
    let valid_owned_vrs_filter = |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd);
    let managed_vrs_list = vrs_list.filter(valid_owned_vrs_filter);
    assert(new_vrs_or_none is Some);
    let new_vrs = new_vrs_or_none->0;
    assert forall |vrs| #[trigger] vrs_list.contains(vrs) implies vrs.metadata.uid is Some by {
        let i = choose |i: int| 0 <= i < vrs_list.len() && vrs_list[i] == vrs;
        VReplicaSetView::marshal_preserves_metadata();
        assert(resp_objs.contains(resp_objs[i])); // trigger
        assert(VReplicaSetView::unmarshal(resp_objs[i]) is Ok);
        assert(vrs_list[i] == VReplicaSetView::unmarshal(resp_objs[i])->Ok_0);
    }
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies vrs.metadata.uid is Some by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, valid_owned_vrs_filter);
    }
    let old_vrs_list_filter_with_new_vrs = |vrs: VReplicaSetView| {
        &&& new_vrs_or_none is None || vrs.metadata.uid != new_vrs.metadata.uid
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    let another_filter_used_in_esr = |vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    assert(old_vrs_list == managed_vrs_list.filter(old_vrs_list_filter_with_new_vrs));
    // because in reconciler we don't know all objects has uid, which is guaranteed by cluster env predicates
    // so the filter in reconciler didn't use uid->0
    assert(managed_vrs_list.filter(old_vrs_list_filter_with_new_vrs) == managed_vrs_list.filter(another_filter_used_in_esr)) by {
        assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies
            (old_vrs_list_filter_with_new_vrs(vrs) == another_filter_used_in_esr(vrs)) by {
            assert(vrs.metadata.uid is Some);
            assert(new_vrs_uid is Some);
            assert(new_vrs.metadata.uid == new_vrs_uid);
        }
        same_filter_implies_same_result(managed_vrs_list, old_vrs_list_filter_with_new_vrs, another_filter_used_in_esr);
    }
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies vrs_list.contains(vrs) && valid_owned_vrs(vrs, vd) by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, valid_owned_vrs_filter);
    }
    assert forall |vrs: VReplicaSetView| #[trigger] old_vrs_list.contains(vrs) implies
        vrs_list.contains(vrs) && valid_owned_vrs(vrs, vd) && s.resources().contains_key(vrs.object_ref()) by {
        seq_filter_is_a_subset_of_original_seq(managed_vrs_list, old_vrs_list_filter_with_new_vrs);
    }
    assert(managed_vrs_list.contains(new_vrs) && vrs_list.contains(new_vrs) && valid_owned_vrs(new_vrs, vd) && match_template_without_hash(vd.spec.template)(new_vrs)) by {
        assert(managed_vrs_list.contains(new_vrs) && match_template_without_hash(vd.spec.template)(new_vrs)) by { // trigger
            // unwrap filter_old_and_new_vrs
            let non_zero_replicas_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
            if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).len() > 0 {
                seq_filter_is_a_subset_of_original_seq(managed_vrs_list, match_template_without_hash(vd.spec.template));
                if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(non_zero_replicas_filter).len() > 0 {
                    assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(non_zero_replicas_filter).contains(new_vrs));
                    seq_filter_is_a_subset_of_original_seq(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)), non_zero_replicas_filter);
                }
                assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).contains(new_vrs));
            } else {
                assert(new_vrs_or_none is None);
                assert(false);
            }
        }
    };
    let map_key = |vrs: VReplicaSetView| vrs.object_ref();
    assert(old_vrs_list.map_values(map_key).no_duplicates()) by { // triggering_cr.well_formed()
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
        lemma_no_duplication_in_resp_objs_implies_no_duplication_in_down_stream(triggering_cr, resp_objs);
    }
    assert(old_vrs_list.map_values(map_key).to_set()
        == filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s))) by {
        lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, new_vrs_uid, s);
    }
    assert(old_vrs_list.len() == 0) by {
        old_vrs_list.map_values(map_key).unique_seq_to_set();
        assert(old_vrs_list.map_values(map_key).len() == old_vrs_list.len());
        assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s)).len() == 0);
    }

    let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    assert(vds_prime.old_vrs_list == old_vrs_list);
    assert(vds_prime.old_vrs_index == old_vrs_list.len());

    // prove local_state_is_coherent_with_etcd_valid_and_coherent(s_prime)
    assert forall |i| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_index
        implies managed_vrs_list.contains(vds_prime.old_vrs_list[i]) by {
        assert(old_vrs_list.contains(vds_prime.old_vrs_list[i])); // trigger
    }
}

}