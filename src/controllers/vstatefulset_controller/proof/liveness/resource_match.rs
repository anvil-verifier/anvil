use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::{spec::prelude::*, error::APIError::*};
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::*},
    cluster::*, 
    message::*
};
use crate::vstatefulset_controller::{
    trusted::{spec_types::*, step::*, liveness_theorem::*, rely},
    model::{install::*, reconciler::*},
    proof::{predicate::*, helper_lemmas::*, helper_invariants, liveness::{api_actions::*, state_predicates::*}, guarantee, shield_lemma},
};
use crate::vstatefulset_controller::trusted::step::VStatefulSetReconcileStepView::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{seq_lib::*, set_lib::*};
use vstd::{seq_lib::*, map_lib::*, multiset::*, relations::*};
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub proof fn lemma_from_init_to_current_state_matches(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
ensures
    spec.entails(lift_state(and!(
            at_vsts_step(vsts, controller_id, at_step![Init]),
            no_pending_req_in_cluster(vsts, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vsts_step(vsts, controller_id, at_step![Done]),
            no_pending_req_in_cluster(vsts, controller_id),
            current_state_matches(vsts)
        )))),
{}

pub proof fn lemma_spec_entails_get_pvc_leads_to_create_or_update_needed(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    pvc_cnt(vsts) > 0, // otherwise GetPVC is unreachable
ensures
    spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, nat0!(), needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id), 
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    )))),
{
    let get_pvc_state_with_index = |pvc_index: nat| lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    ));
    let next_state = lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id), 
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    ));
    let max_minus_one = (pvc_cnt(vsts) - 1) as nat;
    assert forall |i: nat| #![trigger get_pvc_state_with_index(i)] i < max_minus_one
        implies spec.entails(get_pvc_state_with_index(i).leads_to(get_pvc_state_with_index((i + 1) as nat))) by {
        lemma_spec_entails_get_pvc_of_i_leads_to_get_pvc_of_i_plus_one_or_pod_steps(
            vsts, spec, cluster, controller_id, i, needed_index, condemned_len
        );
    }
    leads_to_greater_until_rec(spec,
        get_pvc_state_with_index,
        nat0!(),
        max_minus_one
    );
    assert(spec.entails(get_pvc_state_with_index(max_minus_one).leads_to(next_state))) by {
        lemma_spec_entails_get_pvc_of_i_leads_to_get_pvc_of_i_plus_one_or_pod_steps(
            vsts, spec, cluster, controller_id, max_minus_one, needed_index, condemned_len
        );
    }
    leads_to_trans(spec,
        get_pvc_state_with_index(nat0!()),
        get_pvc_state_with_index(max_minus_one),
        next_state
    );
}

// PVC loop terminates. Proved using rank function on PVC index
pub proof fn lemma_spec_entails_get_pvc_of_i_leads_to_get_pvc_of_i_plus_one_or_pod_steps(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, pvc_index: nat, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    pvc_index < pvc_cnt(vsts), // otherwise GetPVC is unreachable
ensures
    pvc_index + 1 < pvc_cnt(vsts) ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index + nat1!(), needed_index, nat0!(), condemned_len)
    )))),
    pvc_index + 1 == pvc_cnt(vsts) ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id), 
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    )))),
{
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let get_pvc_state = and!(
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    let skip_or_create_pvc_state = and!(
        at_vsts_step(vsts, controller_id, at_step_or![SkipPVC, CreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id), 
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    let skip_pvc_state = and!(
        at_vsts_step(vsts, controller_id, at_step![SkipPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id), 
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    let create_pvc_state = and!(
        at_vsts_step(vsts, controller_id, at_step![CreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id), 
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    let next_state = if pvc_index + 1 < pvc_cnt(vsts) {
        and!(
            at_vsts_step(vsts, controller_id, at_step![GetPVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index + nat1!(), needed_index, nat0!(), condemned_len)
        )
    } else {
        and!(
            at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
            local_state_is_valid_and_coherent(vsts, controller_id), 
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
        )
    };
    lemma_spec_entails_get_pvc_leads_to_skip_or_create_pvc(
        vsts, spec, cluster, controller_id, pvc_index, needed_index, condemned_len
    );
    lemma_spec_entails_skip_pvc_leads_to_create_or_update_needed_or_get_pvc(
        vsts, spec, cluster, controller_id, pvc_index, needed_index, condemned_len
    );
    lemma_spec_entails_create_pvc_leads_to_create_or_update_needed_or_get_pvc(
        vsts, spec, cluster, controller_id, pvc_index, needed_index, condemned_len
    );
    or_leads_to_combine(spec,
        lift_state(skip_pvc_state),
        lift_state(create_pvc_state),
        lift_state(next_state)
    );
    assert(skip_or_create_pvc_state =~= or!(skip_pvc_state, create_pvc_state));
    temp_pred_equality(
        lift_state(skip_or_create_pvc_state),
        lift_state(skip_pvc_state).or(lift_state(create_pvc_state))
    );
    leads_to_trans(spec,
        lift_state(get_pvc_state),
        lift_state(skip_or_create_pvc_state),
        lift_state(next_state)
    );
}

#[verifier(rlimit(100))]
pub proof fn lemma_spec_entails_get_pvc_leads_to_skip_or_create_pvc(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, pvc_index: nat, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
ensures
    spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    ))
    .leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![SkipPVC, CreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    )))),
{
    let get_pvc_state = and!(
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    let after_get_pvc_state_with_req = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterGetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_pvc_req_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    assert(spec.entails(lift_state(get_pvc_state).leads_to(lift_state(after_get_pvc_state_with_req)))) by {
        assert forall |s, s_prime| get_pvc_state(s) && #[trigger] stronger_next(s, s_prime) implies get_pvc_state(s_prime) || after_get_pvc_state_with_req(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                },
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                        lemma_from_get_pvc_to_after_get_pvc(s, s_prime, vsts, cluster, controller_id, pvc_index, needed_index, condemned_len);
                    }
                },
                Step::BuiltinControllersStep(_) => {}, // hardener
                _ => {
                    assert(s_prime.resources() == s.resources());
                }
            }
        }
        let input = (None, Some(vsts.object_ref()));
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, get_pvc_state, after_get_pvc_state_with_req
        );
    }
    let req_msg_is_pending_msg_at_after_get_pvc_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterGetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_pvc_req_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len),
        req_msg_is(msg, vsts.object_ref(), controller_id)
    );
    let after_get_pvc_state_with_resp = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterGetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_pvc_resp_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(after_get_pvc_state_with_req).leads_to(lift_state(after_get_pvc_state_with_resp)))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(after_get_pvc_state_with_req).satisfied_by(ex) implies
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_get_pvc_state(msg))).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg.unwrap();
            assert(req_msg_is_pending_msg_at_after_get_pvc_state(req_msg)(s));
            assert((|msg| lift_state(req_msg_is_pending_msg_at_after_get_pvc_state(msg)))(req_msg).satisfied_by(ex));
        }
        entails_implies_leads_to(spec,
            lift_state(after_get_pvc_state_with_req),
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_get_pvc_state(msg)))
        );
        assert forall |msg| spec.entails(lift_state(#[trigger] req_msg_is_pending_msg_at_after_get_pvc_state(msg)).leads_to(lift_state(after_get_pvc_state_with_resp))) by {
            assert forall |s, s_prime| req_msg_is_pending_msg_at_after_get_pvc_state(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
                req_msg_is_pending_msg_at_after_get_pvc_state(msg)(s_prime) || after_get_pvc_state_with_resp(s_prime) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {},
                    Step::APIServerStep(input) => {
                        if input == Some(msg) {
                            lemma_get_pvc_request_returns_ok_or_err_response(s, s_prime, vsts, cluster, controller_id, msg);
                        } else {
                            lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                        }
                    },
                    Step::BuiltinControllersStep(_) => {}, // hardener
                    _ => {
                        // also hardener, I have to guess which hardener works here
                        assert(s_prime.in_flight().contains(msg));
                        assert(s_prime.resources() == s.resources());
                    }
                }
            }
            let input = Some(msg);
            assert forall |s, s_prime| req_msg_is_pending_msg_at_after_get_pvc_state(msg)(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
                implies after_get_pvc_state_with_resp(s_prime) by {
                lemma_get_pvc_request_returns_ok_or_err_response(s, s_prime, vsts, cluster, controller_id, msg);
            }
            cluster.lemma_pre_leads_to_post_by_api_server(
                spec, input, stronger_next, APIServerStep::HandleRequest, req_msg_is_pending_msg_at_after_get_pvc_state(msg), after_get_pvc_state_with_resp
            );
        }
        leads_to_exists_intro(spec,
            |msg| lift_state(req_msg_is_pending_msg_at_after_get_pvc_state(msg)),
            lift_state(after_get_pvc_state_with_resp)
        );
        leads_to_trans(spec,
            lift_state(after_get_pvc_state_with_req),
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_get_pvc_state(msg))),
            lift_state(after_get_pvc_state_with_resp)
        );
    }
    let resp_msg_is_pending_msg_at_after_get_pvc_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterGetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        resp_msg_is_pending_get_pvc_resp_in_flight(vsts, controller_id, msg),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    let skip_or_create_pvc_state = and!(
        at_vsts_step(vsts, controller_id, at_step_or![SkipPVC, CreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(after_get_pvc_state_with_resp).leads_to(lift_state(skip_or_create_pvc_state)))) by {
        assert forall |ex| #[trigger] lift_state(after_get_pvc_state_with_resp).satisfied_by(ex) implies
            tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_get_pvc_state(msg))).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
            let resp_msg = choose |resp_msg: Message| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg.content.is_get_response()
                &&& resp_msg.content.get_get_response().res is Err
                    ==> resp_msg.content.get_get_response().res->Err_0 == ObjectNotFound
                &&& resp_msg.content.get_get_response().res is Ok
                    ==> s.resources().contains_key(req_msg.content.get_get_request().key())
            };
            assert((|msg| lift_state(resp_msg_is_pending_msg_at_after_get_pvc_state(msg)))(resp_msg).satisfied_by(ex));
        }
        entails_implies_leads_to(spec,
            lift_state(after_get_pvc_state_with_resp),
            tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_get_pvc_state(msg)))
        );
        assert forall |msg| spec.entails(lift_state(#[trigger] resp_msg_is_pending_msg_at_after_get_pvc_state(msg)).leads_to(lift_state(skip_or_create_pvc_state))) by {
            assert forall |s, s_prime| resp_msg_is_pending_msg_at_after_get_pvc_state(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
                resp_msg_is_pending_msg_at_after_get_pvc_state(msg)(s_prime) || skip_or_create_pvc_state(s_prime) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        VStatefulSetReconcileState::marshal_preserves_integrity();
                        lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                        assert(resp_msg_is_pending_get_pvc_resp_in_flight(vsts, controller_id, msg)(s_prime)) by {
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
                            assert(s_prime.in_flight().contains(msg) && resp_msg_matches_req_msg(msg, req_msg)); // hardener
                            if msg.content.get_get_response().res is Ok {
                                let key = req_msg.content.get_get_request().key();
                                assert(s_prime.resources().contains_key(key)) by {
                                    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
                                    let i = (local_state.pvc_index, local_state.needed_index);
                                    // trigger
                                    assert(key.name == pvc_name(vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0, vsts.metadata.name->0, i.1));
                                    pvc_name_with_vsts_match_vsts(key.name, vsts);
                                    assert(s.resources().contains_key(key)); // trigger
                                    assert(({
                                        &&& key.kind == Kind::PersistentVolumeClaimKind
                                        &&& key.namespace == vsts.metadata.namespace->0
                                        &&& pvc_name_match(key.name, vsts.metadata.name->0)
                                    })); // pre of lemma_no_interference
                                    shield_lemma::lemma_no_interference(s, s_prime, vsts, cluster, controller_id, input->0);
                                }
                            }
                        }
                    },
                    Step::ControllerStep(input) => {
                        if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                            lemma_from_get_pvc_resp_to_next_state(s, s_prime, vsts, cluster, controller_id, pvc_index, msg, needed_index, condemned_len);
                            assert(skip_or_create_pvc_state(s_prime));
                        }
                    },
                    Step::BuiltinControllersStep(_) => {}, // hardener
                    _ => {
                        // also hardener, I have to guess which hardener works here
                        assert(s_prime.in_flight().contains(msg));
                        assert(s_prime.resources() == s.resources());
                    }
                }
            }
            let input = (Some(msg), Some(vsts.object_ref()));
            cluster.lemma_pre_leads_to_post_by_controller(
                spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, resp_msg_is_pending_msg_at_after_get_pvc_state(msg), skip_or_create_pvc_state
            );
        }
        leads_to_exists_intro(spec,
            |msg| lift_state(resp_msg_is_pending_msg_at_after_get_pvc_state(msg)),
            lift_state(skip_or_create_pvc_state)
        );
        leads_to_trans(spec,
            lift_state(after_get_pvc_state_with_resp),
            tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_get_pvc_state(msg))),
            lift_state(skip_or_create_pvc_state)
        );
    }
    leads_to_trans_n!(spec,
        lift_state(get_pvc_state),
        lift_state(after_get_pvc_state_with_req),
        lift_state(after_get_pvc_state_with_resp),
        lift_state(skip_or_create_pvc_state)
    );
}

#[verifier(rlimit(100))]
pub proof fn lemma_spec_entails_skip_pvc_leads_to_create_or_update_needed_or_get_pvc(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, pvc_index: nat, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    pvc_index < pvc_cnt(vsts),
ensures
    pvc_index + 1 < pvc_cnt(vsts) ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![SkipPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index + nat1!(), needed_index, nat0!(), condemned_len)
    )))),
    pvc_index + 1 == pvc_cnt(vsts) ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![SkipPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    ))))
{
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let skip_pvc_state = and!(
        at_vsts_step(vsts, controller_id, at_step![SkipPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    let next_state = if pvc_index + 1 < pvc_cnt(vsts) {
        and!(
            at_vsts_step(vsts, controller_id, at_step![GetPVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index + nat1!(), needed_index, nat0!(), condemned_len)
        )
    } else {
        and!(
            at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
        )
    };
    assert(spec.entails(lift_state(skip_pvc_state).leads_to(lift_state(next_state)))) by {
        assert forall |s, s_prime| skip_pvc_state(s) && #[trigger] stronger_next(s, s_prime) implies
            skip_pvc_state(s_prime) || next_state(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                },
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                        lemma_from_skip_pvc_to_next_state(s, s_prime, vsts, cluster, controller_id, pvc_index, needed_index, condemned_len);
                    }
                },
                _ => {
                    assert(s.resources() == s_prime.resources());
                }
            }
        }
        let input = (None, Some(vsts.object_ref()));
        assert forall |s, s_prime| skip_pvc_state(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime)
            implies next_state(s_prime) by {
            lemma_from_skip_pvc_to_next_state(s, s_prime, vsts, cluster, controller_id, pvc_index, needed_index, condemned_len);
        }
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, skip_pvc_state, next_state
        );
    }
}

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
pub proof fn lemma_spec_entails_create_pvc_leads_to_create_or_update_needed_or_get_pvc(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, pvc_index: nat, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    pvc_index < pvc_cnt(vsts),
ensures
    pvc_index + 1 < pvc_cnt(vsts) ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![CreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index + nat1!(), needed_index, nat0!(), condemned_len)
    )))),
    pvc_index + 1 == pvc_cnt(vsts) ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![CreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    ))))
{
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let create_pvc_state = and!(
        at_vsts_step(vsts, controller_id, at_step![CreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    let after_create_pvc_state_with_request = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_create_pvc_req_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index + nat1!(), needed_index, nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(create_pvc_state).leads_to(lift_state(after_create_pvc_state_with_request)))) by {
        assert forall |s, s_prime| create_pvc_state(s) && #[trigger] stronger_next(s, s_prime) implies
            create_pvc_state(s_prime) || after_create_pvc_state_with_request(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                },
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                        lemma_from_create_pvc_to_after_create_pvc(s, s_prime, vsts, cluster, controller_id, pvc_index, needed_index, condemned_len);
                    }
                },
                _ => {}
            }
        }
        let input = (None, Some(vsts.object_ref()));
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, create_pvc_state, after_create_pvc_state_with_request
        );
    }
    let req_msg_is_pending_msg_at_after_create_pvc_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_create_pvc_req_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index + nat1!(), needed_index, nat0!(), condemned_len),
        req_msg_is(msg, vsts.object_ref(), controller_id)
    );
    let after_create_pvc_state_with_response = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_create_pvc_resp_msg_in_flight_and_created_pvc_exists(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index + nat1!(), needed_index, nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(after_create_pvc_state_with_request).leads_to(lift_state(after_create_pvc_state_with_response)))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(after_create_pvc_state_with_request).satisfied_by(ex) implies
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_create_pvc_state(msg))).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg.unwrap();
            assert((|msg| lift_state(req_msg_is_pending_msg_at_after_create_pvc_state(msg)))(req_msg).satisfied_by(ex));
        }
        entails_implies_leads_to(spec,
            lift_state(after_create_pvc_state_with_request),
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_create_pvc_state(msg)))
        );
        assert forall |msg| spec.entails(lift_state(#[trigger] req_msg_is_pending_msg_at_after_create_pvc_state(msg)).leads_to(lift_state(after_create_pvc_state_with_response))) by {
            assert forall |s, s_prime| req_msg_is_pending_msg_at_after_create_pvc_state(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
                req_msg_is_pending_msg_at_after_create_pvc_state(msg)(s_prime) || after_create_pvc_state_with_response(s_prime) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        if input == Some(msg) {
                            lemma_create_pvc_request_returns_ok_or_already_exists_err_response(s, s_prime, vsts, cluster, controller_id, msg);
                            assert(after_create_pvc_state_with_response(s_prime));
                        } else {
                            lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                            assert(req_msg_is_pending_msg_at_after_create_pvc_state(msg)(s_prime));
                        }
                    },
                    // hardeners, this part is flaky
                    Step::BuiltinControllersStep(_) => {},
                    Step::ScheduleControllerReconcileStep(_) => {},
                    _ => {
                        assert(s_prime.in_flight().contains(msg));
                        assert(s_prime.resources() == s.resources());
                    }
                }
            }
            let input = Some(msg);
            assert forall |s, s_prime| req_msg_is_pending_msg_at_after_create_pvc_state(msg)(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
                implies after_create_pvc_state_with_response(s_prime) by {
                lemma_create_pvc_request_returns_ok_or_already_exists_err_response(s, s_prime, vsts, cluster, controller_id, msg);
            }
            cluster.lemma_pre_leads_to_post_by_api_server(
                spec, input, stronger_next, APIServerStep::HandleRequest, req_msg_is_pending_msg_at_after_create_pvc_state(msg), after_create_pvc_state_with_response
            );
        }
        leads_to_exists_intro(spec,
            |msg| lift_state(req_msg_is_pending_msg_at_after_create_pvc_state(msg)),
            lift_state(after_create_pvc_state_with_response)
        );
        leads_to_trans(spec,
            lift_state(after_create_pvc_state_with_request),
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_create_pvc_state(msg))),
            lift_state(after_create_pvc_state_with_response)
        );
    }
    assert(spec.entails(lift_state(after_create_pvc_state_with_response).leads_to(lift_state(
        after_handle_create_or_skip_pvc_helper(vsts, controller_id, pvc_index + 1, needed_index, condemned_len)
    )))) by {
        lemma_spec_entails_after_create_pvc_leads_to_create_or_update_needed_or_get_pvc(
            vsts, spec, cluster, controller_id, pvc_index + 1, needed_index, condemned_len
        );
    }
    leads_to_trans_n!(spec,
        lift_state(create_pvc_state),
        lift_state(after_create_pvc_state_with_request),
        lift_state(after_create_pvc_state_with_response),
        lift_state(after_handle_create_or_skip_pvc_helper(vsts, controller_id, pvc_index + 1, needed_index, condemned_len))
    );
}

pub proof fn lemma_spec_entails_after_create_pvc_leads_to_create_or_update_needed_or_get_pvc(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, pvc_index: nat, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    0 < pvc_index <= pvc_cnt(vsts),
ensures
    spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_create_pvc_resp_msg_in_flight_and_created_pvc_exists(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(
        after_handle_create_or_skip_pvc_helper(vsts, controller_id, pvc_index, needed_index, condemned_len)
    ))),
{
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let after_create_pvc_state_with_response = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_create_pvc_resp_msg_in_flight_and_created_pvc_exists(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    let resp_msg_is_pending_msg_at_after_create_pvc_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        resp_msg_is_pending_create_pvc_resp_in_flight_and_created_pvc_exists(vsts, controller_id, msg),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)
    );
    assert forall |ex| #[trigger] lift_state(after_create_pvc_state_with_response).satisfied_by(ex) implies
        tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_create_pvc_state(msg))).satisfied_by(ex) by {
        let s = ex.head();
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let resp_msg = choose |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_create_response()
            &&& resp_msg.content.get_create_response().res is Err
                ==> resp_msg.content.get_create_response().res->Err_0 == ObjectAlreadyExists
        };
        assert((|msg| lift_state(resp_msg_is_pending_msg_at_after_create_pvc_state(msg)))(resp_msg).satisfied_by(ex));
    }
    entails_implies_leads_to(spec,
        lift_state(after_create_pvc_state_with_response),
        tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_create_pvc_state(msg)))
    );
    assert forall |msg| spec.entails(lift_state(#[trigger] resp_msg_is_pending_msg_at_after_create_pvc_state(msg)).leads_to(
        lift_state(after_handle_create_or_skip_pvc_helper(vsts, controller_id, pvc_index, needed_index, condemned_len)))) by {
        assert forall |s, s_prime| resp_msg_is_pending_msg_at_after_create_pvc_state(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
            resp_msg_is_pending_msg_at_after_create_pvc_state(msg)(s_prime) || after_handle_create_or_skip_pvc_helper(vsts, controller_id, pvc_index, needed_index, condemned_len)(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                        lemma_from_after_create_pvc_to_next_state(s, s_prime, vsts, cluster, controller_id, pvc_index, needed_index, condemned_len);
                        assert(after_handle_create_or_skip_pvc_helper(vsts, controller_id, pvc_index, needed_index, condemned_len)(s_prime));
                    }
                },
                Step::APIServerStep(input) => {
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                    let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
                    let key = req_msg.content.get_create_request().key();
                    assert(s.resources().contains_key(key)); // trigger
                    assert(s_prime.resources().contains_key(key)) by {
                        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
                        let i = ((local_state.pvc_index - 1) as nat, local_state.needed_index);
                        // trigger
                        assert(key.name == pvc_name(vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0, vsts.metadata.name->0, i.1));
                        pvc_name_with_vsts_match_vsts(key.name, vsts);
                        assert(s.resources().contains_key(key)); // trigger
                        assert(({
                            &&& key.kind == Kind::PersistentVolumeClaimKind
                            &&& key.namespace == vsts.metadata.namespace->0
                            &&& pvc_name_match(key.name, vsts.metadata.name->0)
                        })); // pre of lemma_no_interference
                        shield_lemma::lemma_no_interference(s, s_prime, vsts, cluster, controller_id, input->0);
                    }
                },
                Step::BuiltinControllersStep(_) => {}, // hardener
                _ => {
                    // also hardener, I have to guess which hardener works here
                    assert(s_prime.in_flight().contains(msg));
                    assert(s_prime.resources() == s.resources());
                }
            }
        }
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, (Some(msg), Some(vsts.object_ref())), stronger_next, ControllerStep::ContinueReconcile, resp_msg_is_pending_msg_at_after_create_pvc_state(msg), after_handle_create_or_skip_pvc_helper(vsts, controller_id, pvc_index, needed_index, condemned_len)
        );
    }
    leads_to_exists_intro(spec,
        |msg| lift_state(resp_msg_is_pending_msg_at_after_create_pvc_state(msg)),
        lift_state(after_handle_create_or_skip_pvc_helper(vsts, controller_id, pvc_index, needed_index, condemned_len))
    );
    leads_to_trans(spec,
        lift_state(after_create_pvc_state_with_response),
        tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_create_pvc_state(msg))),
        lift_state(after_handle_create_or_skip_pvc_helper(vsts, controller_id, pvc_index, needed_index, condemned_len))
    );
}

pub proof fn lemma_spec_entails_create_or_update_needed_leads_to_delete_condemned_or_outdated(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    replicas(vsts) > 0, // otherwise Create/UpdateNeeded steps are not reachable
ensures
    condemned_len > 0 ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), nat0!(), nat0!(), condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), nat0!(), condemned_len)
    )))),
    condemned_len == 0 ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), nat0!(), nat0!(), condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![DeleteOutdated]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), nat0!(), nat0!())
    )))),
{
    let create_or_update_needed_state_with_needed_index = |needed_index: nat| and!(
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    );
    let create_needed_state_with_needed_index = |needed_index: nat| and!(
        at_vsts_step(vsts, controller_id, at_step![CreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    );
    let update_needed_state_with_needed_index = |needed_index: nat| and!(
        at_vsts_step(vsts, controller_id, at_step![UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    );
    let delete_condemned_or_outdated_state = if condemned_len > 0 {
        and!(
            at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), nat0!(), condemned_len)
        )
    } else {
        and!(
            at_vsts_step(vsts, controller_id, at_step![DeleteOutdated]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), nat0!(), nat0!())
        )
    };
    let max_minus_one = (replicas(vsts) - 1) as nat;
    assert forall |needed_index: nat| needed_index < max_minus_one implies spec.entails(lift_state(#[trigger] create_or_update_needed_state_with_needed_index(needed_index))
        .leads_to(lift_state(create_or_update_needed_state_with_needed_index(needed_index + 1)))) by {
        lemma_spec_entails_create_needed_pod_of_i_leads_to_get_pvc_or_delete_condemned_or_create_or_update_of_i_plus_one(
            vsts, spec, cluster, controller_id, needed_index, condemned_len
        );
        lemma_spec_entails_updated_needed_pod_of_i_leads_to_get_pvc_or_delete_condemned_or_create_or_update_of_i_plus_one(
            vsts, spec, cluster, controller_id, needed_index, condemned_len
        );
        temp_pred_equality(
            lift_state(create_or_update_needed_state_with_needed_index(needed_index)),
            lift_state(create_needed_state_with_needed_index(needed_index)).or(lift_state(update_needed_state_with_needed_index(needed_index)))
        );
        if pvc_cnt(vsts) > 0 {
            let get_pvc_state = and!(
                at_vsts_step(vsts, controller_id, at_step![GetPVC]),
                local_state_is_valid_and_coherent(vsts, controller_id),
                no_pending_req_in_cluster(vsts, controller_id),
                pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, nat0!(), needed_index + nat1!(), nat0!(), condemned_len)
            );
            or_leads_to_combine(spec,
                lift_state(create_needed_state_with_needed_index(needed_index)),
                lift_state(update_needed_state_with_needed_index(needed_index)),
                lift_state(get_pvc_state)
            );
            lemma_spec_entails_get_pvc_leads_to_create_or_update_needed(
                vsts, spec, cluster, controller_id, needed_index + 1, condemned_len
            );
            leads_to_trans(spec,
                lift_state(create_or_update_needed_state_with_needed_index(needed_index)),
                lift_state(get_pvc_state),
                lift_state(create_or_update_needed_state_with_needed_index(needed_index + 1))
            );
        } else {
            or_leads_to_combine(spec,
                lift_state(create_needed_state_with_needed_index(needed_index)),
                lift_state(update_needed_state_with_needed_index(needed_index)),
                lift_state(create_or_update_needed_state_with_needed_index(needed_index + 1))
            );
        }
    }
    leads_to_greater_until_rec(spec,
        |needed_index| lift_state(create_or_update_needed_state_with_needed_index(needed_index)),
        nat0!(),
        max_minus_one
    );
    assert(spec.entails(lift_state(create_or_update_needed_state_with_needed_index(max_minus_one)).leads_to(lift_state(delete_condemned_or_outdated_state)))) by {
        temp_pred_equality(
            lift_state(create_or_update_needed_state_with_needed_index(max_minus_one)),
            lift_state(create_needed_state_with_needed_index(max_minus_one)).or(lift_state(update_needed_state_with_needed_index(max_minus_one)))
        );
        lemma_spec_entails_create_needed_pod_of_i_leads_to_get_pvc_or_delete_condemned_or_create_or_update_of_i_plus_one(
            vsts, spec, cluster, controller_id, max_minus_one, condemned_len
        );
        lemma_spec_entails_updated_needed_pod_of_i_leads_to_get_pvc_or_delete_condemned_or_create_or_update_of_i_plus_one(
            vsts, spec, cluster, controller_id, max_minus_one, condemned_len
        );
        or_leads_to_combine(spec,
            lift_state(create_needed_state_with_needed_index(max_minus_one)),
            lift_state(update_needed_state_with_needed_index(max_minus_one)),
            lift_state(delete_condemned_or_outdated_state)
        );
    }
    leads_to_trans(spec,
        lift_state(create_or_update_needed_state_with_needed_index(nat0!())),
        lift_state(create_or_update_needed_state_with_needed_index(max_minus_one)),
        lift_state(delete_condemned_or_outdated_state)
    );
}

#[verifier(rlimit(50))]
#[verifier(spinoff_prover)]
pub proof fn lemma_spec_entails_create_needed_pod_of_i_leads_to_get_pvc_or_delete_condemned_or_create_or_update_of_i_plus_one(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    needed_index < replicas(vsts),
ensures
    spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![CreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(
        after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index + nat1!(), condemned_len)
    ))),
{
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let create_needed_state = and!(
        at_vsts_step(vsts, controller_id, at_step![CreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    );
    let after_create_needed_state_with_request = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_create_needed_pod_req_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index + nat1!(), nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(create_needed_state).leads_to(lift_state(after_create_needed_state_with_request)))) by {
        assert forall |s, s_prime| create_needed_state(s) && #[trigger] stronger_next(s, s_prime) implies
            create_needed_state(s_prime) || after_create_needed_state_with_request(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                },
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                        lemma_from_create_needed_to_after_create_needed(s, s_prime, vsts, cluster, controller_id, needed_index, condemned_len);
                    }
                },
                _ => {}
            }
        }
        let input = (None, Some(vsts.object_ref()));
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, create_needed_state, after_create_needed_state_with_request
        );
    }
    let req_msg_is_pending_msg_at_after_create_needed_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_create_needed_pod_req_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index + nat1!(), nat0!(), condemned_len),
        req_msg_is(msg, vsts.object_ref(), controller_id)
    );
    let after_create_needed_state_with_response = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_create_needed_pod_resp_in_flight_and_created_pod_exists(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index + nat1!(), nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(after_create_needed_state_with_request).leads_to(lift_state(after_create_needed_state_with_response)))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(after_create_needed_state_with_request).satisfied_by(ex) implies
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_create_needed_state(msg))).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg.unwrap();
            assert((|msg| lift_state(req_msg_is_pending_msg_at_after_create_needed_state(msg)))(req_msg).satisfied_by(ex));
        }
        entails_implies_leads_to(spec,
            lift_state(after_create_needed_state_with_request),
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_create_needed_state(msg)))
        );
        assert forall |msg| spec.entails(lift_state(#[trigger] req_msg_is_pending_msg_at_after_create_needed_state(msg)).leads_to(lift_state(after_create_needed_state_with_response))) by {
            assert forall |s, s_prime| req_msg_is_pending_msg_at_after_create_needed_state(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
                req_msg_is_pending_msg_at_after_create_needed_state(msg)(s_prime) || after_create_needed_state_with_response(s_prime) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        if input == Some(msg) {
                            lemma_from_after_send_create_needed_pod_req_to_receive_create_needed_pod_resp(s, s_prime, vsts, cluster, controller_id, msg, needed_index + nat1!(), condemned_len);
                            assert(after_create_needed_state_with_response(s_prime));
                        } else {
                            lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                        }
                    },
                    Step::BuiltinControllersStep(_) => {},
                    Step::ScheduleControllerReconcileStep(_) => {},
                    _ => {
                        assert(s_prime.in_flight().contains(msg));
                        assert(s_prime.resources() == s.resources());
                    }
                }
            }
            let input = Some(msg);
            assert forall |s, s_prime| req_msg_is_pending_msg_at_after_create_needed_state(msg)(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
                implies after_create_needed_state_with_response(s_prime) by {
                lemma_create_needed_pod_request_returns_ok_response(s, s_prime, vsts, cluster, controller_id, msg);
            }
            cluster.lemma_pre_leads_to_post_by_api_server(
                spec, input, stronger_next, APIServerStep::HandleRequest, req_msg_is_pending_msg_at_after_create_needed_state(msg), after_create_needed_state_with_response
            );
        }
        leads_to_exists_intro(spec,
            |msg| lift_state(req_msg_is_pending_msg_at_after_create_needed_state(msg)),
            lift_state(after_create_needed_state_with_response)
        );
        leads_to_trans(spec,
            lift_state(after_create_needed_state_with_request),
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_create_needed_state(msg))),
            lift_state(after_create_needed_state_with_response)
        );
    }
    let resp_msg_is_pending_msg_at_after_create_needed_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        resp_msg_is_pending_create_needed_pod_resp_in_flight_and_created_pod_exists(vsts, controller_id, msg),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index + nat1!(), nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(after_create_needed_state_with_response).leads_to(lift_state(
        after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index + nat1!(), condemned_len)
    )))) by {
        lemma_spec_entails_after_create_needed_leads_to_next_state(
            vsts, spec, cluster, controller_id, needed_index + 1, condemned_len
        );
    }
    leads_to_trans_n!(spec,
        lift_state(create_needed_state),
        lift_state(after_create_needed_state_with_request),
        lift_state(after_create_needed_state_with_response),
        lift_state(after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index + nat1!(), condemned_len))
    );
}

#[verifier(rlimit(50))]
pub proof fn lemma_spec_entails_after_create_needed_leads_to_next_state(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    0 < needed_index <= replicas(vsts),
ensures
    spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_create_needed_pod_resp_in_flight_and_created_pod_exists(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(
        after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)
    ))),
{
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let after_create_needed_state_with_response = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_create_needed_pod_resp_in_flight_and_created_pod_exists(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    );
    let resp_msg_is_pending_msg_at_after_create_needed_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        resp_msg_is_pending_create_needed_pod_resp_in_flight_and_created_pod_exists(vsts, controller_id, msg),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    );
    assert forall |ex| #[trigger] lift_state(after_create_needed_state_with_response).satisfied_by(ex) implies
        tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_create_needed_state(msg))).satisfied_by(ex) by {
        let s = ex.head();
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let resp_msg = choose |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_create_response()
            &&& resp_msg.content.get_create_response().res is Err
                ==> resp_msg.content.get_create_response().res->Err_0 == ObjectAlreadyExists
        };
        assert((|msg| lift_state(resp_msg_is_pending_msg_at_after_create_needed_state(msg)))(resp_msg).satisfied_by(ex));
    }
    entails_implies_leads_to(spec,
        lift_state(after_create_needed_state_with_response),
        tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_create_needed_state(msg)))
    );
    assert forall |msg| spec.entails(lift_state(#[trigger] resp_msg_is_pending_msg_at_after_create_needed_state(msg)).leads_to(lift_state(
        after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)
    ))) by {
        assert forall |s, s_prime| resp_msg_is_pending_msg_at_after_create_needed_state(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
            resp_msg_is_pending_msg_at_after_create_needed_state(msg)(s_prime) || after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                        lemma_from_create_needed_pod_resp_to_next_state(s, s_prime, vsts, cluster, controller_id, msg, needed_index, condemned_len);
                        assert(after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)(s_prime));
                    }
                },
                Step::APIServerStep(input) => { // slowest part, we can harden this by creating another proof with coherence predicate hidden
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                    let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
                    let key = req_msg.content.get_create_request().key();
                    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
                    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                    assert(s_prime.resources().contains_key(key) && weakly_eq(s_prime.resources()[key], s.resources()[key])) by {
                        assert(key.name == pod_name(vsts.metadata.name->0, (needed_index - 1) as nat));
                        assert(({
                            &&& s.resources().contains_key(key) // trigger
                            &&& key.kind == Kind::PodKind
                            &&& key.namespace == vsts.metadata.namespace->0
                            &&& pod_name_match(key.name, vsts.metadata.name->0)
                        })); // pre of lemma_no_interference
                        shield_lemma::lemma_no_interference(s, s_prime, vsts, cluster, controller_id, input->0);
                    }
                },
                _ => {
                    assert(s_prime.in_flight().contains(msg));
                    assert(s_prime.resources() == s.resources());
                }
            }
        }
        let input = (Some(msg), Some(vsts.object_ref()));
        assert forall |s, s_prime| resp_msg_is_pending_msg_at_after_create_needed_state(msg)(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime)
            implies after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)(s_prime) by {
            lemma_from_create_needed_pod_resp_to_next_state(s, s_prime, vsts, cluster, controller_id, msg, needed_index, condemned_len);
        }
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, resp_msg_is_pending_msg_at_after_create_needed_state(msg),
            after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)
        );
    }
    leads_to_exists_intro(spec,
        |msg| lift_state(resp_msg_is_pending_msg_at_after_create_needed_state(msg)),
        lift_state(after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len))
    );
    leads_to_trans(spec,
        lift_state(after_create_needed_state_with_response),
        tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_create_needed_state(msg))),
        lift_state(after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len))
    );
}

#[verifier(rlimit(50))]
pub proof fn lemma_spec_entails_updated_needed_pod_of_i_leads_to_get_pvc_or_delete_condemned_or_create_or_update_of_i_plus_one(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    needed_index < replicas(vsts),
ensures
    spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(
        after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index + nat1!(), condemned_len)
    ))),
{
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let update_needed_state = and!(
        at_vsts_step(vsts, controller_id, at_step![UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    );
    let after_update_needed_state_with_request = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_update_needed_pod_req_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index + nat1!(), nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(update_needed_state).leads_to(lift_state(after_update_needed_state_with_request)))) by {
        assert forall |s, s_prime| update_needed_state(s) && #[trigger] stronger_next(s, s_prime) implies
            update_needed_state(s_prime) || after_update_needed_state_with_request(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                },
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                        lemma_from_update_needed_to_after_update_needed(s, s_prime, vsts, cluster, controller_id, needed_index, condemned_len);
                    }
                },
                _ => {}
            }
        }
        let input = (None, Some(vsts.object_ref()));
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, update_needed_state, after_update_needed_state_with_request
        );
    }
    let req_msg_is_pending_msg_at_after_update_needed_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_update_needed_pod_req_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index + nat1!(), nat0!(), condemned_len),
        req_msg_is(msg, vsts.object_ref(), controller_id)
    );
    let after_update_needed_state_with_response = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_update_needed_pod_resp_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index + nat1!(), nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(after_update_needed_state_with_request).leads_to(lift_state(after_update_needed_state_with_response)))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(after_update_needed_state_with_request).satisfied_by(ex) implies
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_update_needed_state(msg))).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg.unwrap();
            assert((|msg| lift_state(req_msg_is_pending_msg_at_after_update_needed_state(msg)))(req_msg).satisfied_by(ex));
        }
        entails_implies_leads_to(spec,
            lift_state(after_update_needed_state_with_request),
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_update_needed_state(msg)))
        );
        assert forall |msg| spec.entails(lift_state(#[trigger] req_msg_is_pending_msg_at_after_update_needed_state(msg)).leads_to(lift_state(after_update_needed_state_with_response))) by {
            assert forall |s, s_prime| req_msg_is_pending_msg_at_after_update_needed_state(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
                req_msg_is_pending_msg_at_after_update_needed_state(msg)(s_prime) || after_update_needed_state_with_response(s_prime) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        if input == Some(msg) {
                            lemma_from_after_send_get_then_update_needed_pod_req_to_receive_get_then_update_needed_pod_resp(s, s_prime, vsts, cluster, controller_id, msg, needed_index + nat1!(), condemned_len);
                            assert(after_update_needed_state_with_response(s_prime));
                        } else {
                            lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                        }
                    },
                    Step::BuiltinControllersStep(_) => {},
                    Step::ScheduleControllerReconcileStep(_) => {},
                    _ => {
                        assert(s_prime.in_flight().contains(msg));
                        assert(s_prime.resources() == s.resources());
                    }
                }
            }
            let input = Some(msg);
            assert forall |s, s_prime| req_msg_is_pending_msg_at_after_update_needed_state(msg)(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
                implies after_update_needed_state_with_response(s_prime) by {
                lemma_get_then_update_needed_pod_request_returns_ok_response(s, s_prime, vsts, cluster, controller_id, msg);
            }
            cluster.lemma_pre_leads_to_post_by_api_server(
                spec, input, stronger_next, APIServerStep::HandleRequest, req_msg_is_pending_msg_at_after_update_needed_state(msg), after_update_needed_state_with_response
            );
        }
        leads_to_exists_intro(spec,
            |msg| lift_state(req_msg_is_pending_msg_at_after_update_needed_state(msg)),
            lift_state(after_update_needed_state_with_response)
        );
        leads_to_trans(spec,
            lift_state(after_update_needed_state_with_request),
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_update_needed_state(msg))),
            lift_state(after_update_needed_state_with_response)
        );
    }
    let resp_msg_is_pending_msg_at_after_update_needed_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        resp_msg_is_pending_get_then_update_needed_pod_resp_in_flight(vsts, controller_id, msg),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index + nat1!(), nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(after_update_needed_state_with_response).leads_to(lift_state(
        after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index + nat1!(), condemned_len)
    )))) by {
        lemma_spec_entails_after_update_needed_leads_to_next_state(
            vsts, spec, cluster, controller_id, needed_index + 1, condemned_len
        );
    }
    leads_to_trans_n!(spec,
        lift_state(update_needed_state),
        lift_state(after_update_needed_state_with_request),
        lift_state(after_update_needed_state_with_response),
        lift_state(after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index + nat1!(), condemned_len))
    );
}

#[verifier(rlimit(50))]
pub proof fn lemma_spec_entails_after_update_needed_leads_to_next_state(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    0 < needed_index <= replicas(vsts),
ensures
    spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_update_needed_pod_resp_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    )).leads_to(lift_state(
        after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)
    ))),
{
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let after_update_needed_state_with_response = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_update_needed_pod_resp_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    );
    let resp_msg_is_pending_msg_at_after_update_needed_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        resp_msg_is_pending_get_then_update_needed_pod_resp_in_flight(vsts, controller_id, msg),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)
    );
    assert(spec.entails(lift_state(after_update_needed_state_with_response).leads_to(lift_state(
        after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)
    )))) by {
        assert forall |ex| #[trigger] lift_state(after_update_needed_state_with_response).satisfied_by(ex) implies
            tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_update_needed_state(msg))).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
            let resp_msg = choose |resp_msg: Message| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg.content.is_get_then_update_response()
                &&& resp_msg.content.get_get_then_update_response().res is Ok
            };
            assert((|msg| lift_state(resp_msg_is_pending_msg_at_after_update_needed_state(msg)))(resp_msg).satisfied_by(ex));
        }
        entails_implies_leads_to(spec,
            lift_state(after_update_needed_state_with_response),
            tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_update_needed_state(msg)))
        );
        assert forall |msg| spec.entails(lift_state(#[trigger] resp_msg_is_pending_msg_at_after_update_needed_state(msg)).leads_to(lift_state(
            after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)
        ))) by {
            assert forall |s, s_prime| resp_msg_is_pending_msg_at_after_update_needed_state(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
                resp_msg_is_pending_msg_at_after_update_needed_state(msg)(s_prime) || after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)(s_prime) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                            lemma_from_get_then_update_needed_pod_resp_to_next_state(s, s_prime, vsts, cluster, controller_id, msg, needed_index, condemned_len);
                            assert(after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)(s_prime));
                        }
                    },
                    Step::APIServerStep(input) => { // slowest part, we can harden this by creating another proof with coherence predicate hidden
                        lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
                        let key = req_msg.content.get_get_then_update_request().key();
                        let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
                        let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
                        lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                        assert(s_prime.resources().contains_key(key) && weakly_eq(s_prime.resources()[key], s.resources()[key])) by {
                            assert(key.name == pod_name(vsts.metadata.name->0, (needed_index - 1) as nat));
                            assert(({
                                &&& s.resources().contains_key(key) // trigger
                                &&& key.kind == Kind::PodKind
                                &&& key.namespace == vsts.metadata.namespace->0
                                &&& pod_name_match(key.name, vsts.metadata.name->0)
                            })); // pre of lemma_no_interference
                            shield_lemma::lemma_no_interference(s, s_prime, vsts, cluster, controller_id, input->0);
                        }
                    },
                    _ => {
                        assert(s_prime.in_flight().contains(msg));
                        assert(s_prime.resources() == s.resources());
                    }
                }
            }
            let input = (Some(msg), Some(vsts.object_ref()));
            assert forall |s, s_prime| resp_msg_is_pending_msg_at_after_update_needed_state(msg)(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime)
                implies after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)(s_prime) by {
                lemma_from_get_then_update_needed_pod_resp_to_next_state(s, s_prime, vsts, cluster, controller_id, msg, needed_index, condemned_len);
            }
            cluster.lemma_pre_leads_to_post_by_controller(
                spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, resp_msg_is_pending_msg_at_after_update_needed_state(msg),
                after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)
            );
        }
        leads_to_exists_intro(spec,
            |msg| lift_state(resp_msg_is_pending_msg_at_after_update_needed_state(msg)),
            lift_state(after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len))
        );
        leads_to_trans(spec,
            lift_state(after_update_needed_state_with_response),
            tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_update_needed_state(msg))),
            lift_state(after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len))
        );
    }
}

#[verifier(rlimit(100))]
pub proof fn lemma_spec_entails_deleted_condemned_of_i_leads_to_delete_condemned_of_i_plus_one_or_delete_outdated(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, condemned_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    condemned_index < condemned_len,
ensures
    condemned_index + 1 == condemned_len ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![DeleteOutdated]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_len, condemned_len)
    )))),
    condemned_index + 1 < condemned_len ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index + nat1!(), condemned_len
    ))))),
{
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let delete_condemned_state = and!(
        at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)
    );
    let after_delete_condemned_state_with_request = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_delete_condemned_pod_req_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index + nat1!(), condemned_len)
    );
    assert(spec.entails(lift_state(delete_condemned_state).leads_to(lift_state(after_delete_condemned_state_with_request)))) by {
        assert forall |s, s_prime| delete_condemned_state(s) && #[trigger] stronger_next(s, s_prime) implies
            delete_condemned_state(s_prime) || after_delete_condemned_state_with_request(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                },
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                        lemma_from_delete_condemned_to_after_delete_condemned(s, s_prime, vsts, cluster, controller_id, condemned_index, condemned_len);
                    }
                },
                _ => {}
            }
        }
        let input = (None, Some(vsts.object_ref()));
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, delete_condemned_state, after_delete_condemned_state_with_request
        );
    }
    let req_msg_is_pending_msg_at_after_delete_condemned_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_delete_condemned_pod_req_in_flight(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index + nat1!(), condemned_len),
        req_msg_is(msg, vsts.object_ref(), controller_id)
    );
    let after_delete_condemned_state_with_response = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index + nat1!(), condemned_len)
    );
    assert(spec.entails(lift_state(after_delete_condemned_state_with_request).leads_to(lift_state(after_delete_condemned_state_with_response)))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(after_delete_condemned_state_with_request).satisfied_by(ex) implies
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_delete_condemned_state(msg))).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg.unwrap();
            assert((|msg| lift_state(req_msg_is_pending_msg_at_after_delete_condemned_state(msg)))(req_msg).satisfied_by(ex));
        }
        entails_implies_leads_to(spec,
            lift_state(after_delete_condemned_state_with_request),
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_delete_condemned_state(msg)))
        );
        assert forall |msg| spec.entails(lift_state(#[trigger] req_msg_is_pending_msg_at_after_delete_condemned_state(msg)).leads_to(lift_state(after_delete_condemned_state_with_response))) by {
            assert forall |s, s_prime| req_msg_is_pending_msg_at_after_delete_condemned_state(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
                req_msg_is_pending_msg_at_after_delete_condemned_state(msg)(s_prime) || after_delete_condemned_state_with_response(s_prime) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        if input == Some(msg) {
                            lemma_from_after_send_get_then_delete_condemned_pod_req_to_receive_get_then_delete_condemned_pod_resp(s, s_prime, vsts, cluster, controller_id, msg, condemned_index + nat1!(), condemned_len);
                            assert(after_delete_condemned_state_with_response(s_prime));
                        } else {
                            lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                        }
                    },
                    Step::BuiltinControllersStep(_) => {},
                    _ => {
                        assert(s_prime.in_flight().contains(msg));
                        assert(s_prime.resources() == s.resources());
                    }
                }
            }
            let input = Some(msg);
            assert forall |s, s_prime| req_msg_is_pending_msg_at_after_delete_condemned_state(msg)(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
                implies after_delete_condemned_state_with_response(s_prime) by {
                lemma_from_after_send_get_then_delete_condemned_pod_req_to_receive_get_then_delete_condemned_pod_resp(s, s_prime, vsts, cluster, controller_id, msg, condemned_index + nat1!(), condemned_len);
            }
            cluster.lemma_pre_leads_to_post_by_api_server(
                spec, input, stronger_next, APIServerStep::HandleRequest, req_msg_is_pending_msg_at_after_delete_condemned_state(msg), after_delete_condemned_state_with_response
            );
        }
        leads_to_exists_intro(spec,
            |msg| lift_state(req_msg_is_pending_msg_at_after_delete_condemned_state(msg)),
            lift_state(after_delete_condemned_state_with_response)
        );
        leads_to_trans(spec,
            lift_state(after_delete_condemned_state_with_request),
            tla_exists(|msg| lift_state(req_msg_is_pending_msg_at_after_delete_condemned_state(msg))),
            lift_state(after_delete_condemned_state_with_response)
        );
    }
    let delete_condemned_or_outdated_state = if condemned_index + nat1!() == condemned_len {
        and!(
            at_vsts_step(vsts, controller_id, at_step![DeleteOutdated]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_len, condemned_len)
        )
    } else {
        and!(
            at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index + nat1!(), condemned_len)
        )
    };
    assert(spec.entails(lift_state(after_delete_condemned_state_with_response).leads_to(lift_state(delete_condemned_or_outdated_state)))) by {
        lemma_spec_entails_after_delete_condemned_leads_to_delete_condemned_or_delete_outdated(
            vsts, spec, cluster, controller_id, condemned_index + nat1!(), condemned_len
        );
    }
    leads_to_trans_n!(spec,
        lift_state(delete_condemned_state),
        lift_state(after_delete_condemned_state_with_request),
        lift_state(after_delete_condemned_state_with_response),
        lift_state(delete_condemned_or_outdated_state)
    );
}

#[verifier(rlimit(50))]
pub proof fn lemma_spec_entails_after_delete_condemned_leads_to_delete_condemned_or_delete_outdated(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, condemned_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
    0 < condemned_index <= condemned_len,
ensures
    condemned_index < condemned_len ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)
    )))),
    condemned_index == condemned_len ==> spec.entails(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step![DeleteOutdated]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_len, condemned_len)
    )))),
{
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let after_delete_condemned_state_with_response = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(vsts, controller_id),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)
    );
    let resp_msg_is_pending_msg_at_after_delete_condemned_state = |msg| and!(
        at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        resp_msg_is_pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(vsts, controller_id, msg),
        pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)
    );
    let delete_condemned_or_outdated_state = if condemned_index < condemned_len {
        and!(
            at_vsts_step(vsts, controller_id, at_step![DeleteCondemned]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)
        )
    } else {
        and!(
            at_vsts_step(vsts, controller_id, at_step![DeleteOutdated]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_len, condemned_len)
        )
    };
    assert forall |ex| #[trigger] lift_state(after_delete_condemned_state_with_response).satisfied_by(ex) implies
        tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_delete_condemned_state(msg))).satisfied_by(ex) by {
        let s = ex.head();
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        let resp_msg = choose |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.is_get_then_delete_response()
            &&& resp_msg.content.get_get_then_delete_response().res is Err
                ==> resp_msg.content.get_get_then_delete_response().res->Err_0 == ObjectNotFound
        };
        assert((|msg| lift_state(resp_msg_is_pending_msg_at_after_delete_condemned_state(msg)))(resp_msg).satisfied_by(ex));
    }
    entails_implies_leads_to(spec,
        lift_state(after_delete_condemned_state_with_response),
        tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_delete_condemned_state(msg)))
    );
    assert forall |msg| spec.entails(lift_state(#[trigger] resp_msg_is_pending_msg_at_after_delete_condemned_state(msg)).leads_to(lift_state(delete_condemned_or_outdated_state))) by {
        assert forall |s, s_prime| resp_msg_is_pending_msg_at_after_delete_condemned_state(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
            resp_msg_is_pending_msg_at_after_delete_condemned_state(msg)(s_prime) || delete_condemned_or_outdated_state(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                        lemma_from_after_delete_condemned_to_delete_condemned_or_outdated(s, s_prime, vsts, cluster, controller_id, msg, condemned_index, condemned_len);
                        assert(delete_condemned_or_outdated_state(s_prime));
                    }
                },
                Step::APIServerStep(input) => { // slowest part, we can harden this by creating another proof with coherence predicate hidden
                    lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(s, s_prime, vsts, cluster, controller_id, input->0);
                    let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
                    let key = req_msg.content.get_get_then_delete_request().key();
                    if s_prime.resources().contains_key(key) {
                        let ord = get_ordinal(vsts.metadata.name->0, key.name)->0;
                        assert(key.name == pod_name(vsts.metadata.name->0, ord));
                        assert(s.resources().contains_key(key)) by {
                            shield_lemma::lemma_no_interference(s, s_prime, vsts, cluster, controller_id, input->0);
                        }
                        assert(false);
                    }
                },
                _ => {
                    assert(s_prime.in_flight().contains(msg));
                    assert(s_prime.resources() == s.resources());
                }
            }
        }
        let input = (Some(msg), Some(vsts.object_ref()));
        assert forall |s, s_prime| resp_msg_is_pending_msg_at_after_delete_condemned_state(msg)(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime)
            implies delete_condemned_or_outdated_state(s_prime) by {
            lemma_from_after_delete_condemned_to_delete_condemned_or_outdated(s, s_prime, vsts, cluster, controller_id, msg, condemned_index, condemned_len);
        }
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, resp_msg_is_pending_msg_at_after_delete_condemned_state(msg),
            delete_condemned_or_outdated_state
        );
    }
    leads_to_exists_intro(spec,
        |msg| lift_state(resp_msg_is_pending_msg_at_after_delete_condemned_state(msg)),
        lift_state(delete_condemned_or_outdated_state)
    );
    leads_to_trans(spec,
        lift_state(after_delete_condemned_state_with_response),
        tla_exists(|msg| lift_state(resp_msg_is_pending_msg_at_after_delete_condemned_state(msg))),
        lift_state(delete_condemned_or_outdated_state)
    );
}

pub proof fn lemma_from_init_to_after_list_pod(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![Init])(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s_prime),
    pending_list_pod_req_in_flight(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_list_pod_req_to_receive_list_pod_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s),
    pending_list_pod_req_in_flight(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s_prime),
    pending_list_pod_resp_in_flight(vsts, controller_id)(s_prime),
{
    lemma_list_pod_request_returns_ok_with_objs_matching_vsts(
        s, s_prime, vsts, cluster, controller_id
    );
}

// Then, prove at_step_or![GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated] |=
// || at_step![GetPVC] || at_step![CreateNeeded] || at_step![UpdateNeeded] || at_step![DeleteCondemned] || at_step![DeleteOutdated]
// and go to next step with local_state_is_valid_and_coherent
pub proof fn lemma_from_list_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    resp_msg_or_none(s, vsts.object_ref(), controller_id) is Some,
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s),
    pending_list_pod_resp_in_flight(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step_or![GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated])(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
{
    let current_local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let triggering_cr = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).unwrap();
    let resp_msg = resp_msg_or_none(s, vsts.object_ref(), controller_id).unwrap();
    let wrapped_resp = Some(ResponseView::KResponse(resp_msg.content->APIResponse_0));
    let next_local_state = handle_after_list_pod(vsts, wrapped_resp, current_local_state).0;
    let objs = resp_msg.content.get_list_response().res->Ok_0;
    let pods = objects_to_pods(objs)->0;
    VStatefulSetReconcileState::marshal_preserves_integrity();
    VStatefulSetView::marshal_preserves_integrity();
    // assert(objects_to_pods(objs) is Some);
    // assert(pod_filter(vsts) == pod_filter(triggering_cr));
    let next_local_state_from_cluster = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    // for better proof stability
    assert(next_local_state =~= next_local_state_from_cluster) by {
        assert(next_local_state.needed == next_local_state_from_cluster.needed);
        assert(next_local_state.condemned == next_local_state_from_cluster.condemned);
        assert(next_local_state.pvcs == next_local_state_from_cluster.pvcs);
    }
    assert(objs == extract_some_k_list_resp_view(wrapped_resp)->Ok_0);
    assert(next_local_state.reconcile_step != Error);
    let replicas = vsts.spec.replicas.unwrap_or(1) as nat;
    let vsts_name = vsts.metadata.name->0;
    assert(replicas >= 0);
    assert(local_state_is_valid_and_coherent(vsts, controller_id)(s_prime)) by {
        let filtered_pods = pods.filter(pod_filter(vsts));
        let (needed, condemned) = partition_pods(vsts_name, replicas, filtered_pods);
        assert forall |pod: PodView| #[trigger] filtered_pods.contains(pod) implies {
            let obj = s.resources()[pod.object_ref()];
            &&& pod.metadata.name is Some
            &&& pod.metadata.namespace is Some
            &&& pod.metadata.namespace->0 == vsts.metadata.namespace->0
            &&& pod.metadata.owner_references_contains(vsts.controller_owner_ref())
            &&& s.resources().contains_key(pod.object_ref())
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        } by {
            PodView::marshal_preserves_metadata();
            seq_filter_contains_implies_seq_contains(pods, pod_filter(vsts), pod);
            let i = choose |i: int| 0 <= i < pods.len() && pods[i as int] == pod;
            assert(objs.contains(objs[i]));
            // assert(PodView::unmarshal(objs[i]) is Ok);
            // assert(PodView::unmarshal(objs[i])->Ok_0 == pod);
        }
        assert(partition_pods(vsts_name, replicas, filtered_pods) == partition_pods(triggering_cr.metadata.name->0, replicas, filtered_pods));
        // assert(next_local_state.needed == needed);
        // assert(next_local_state.condemned == condemned);
        let condemned_ord_filter = |pod: PodView| get_ordinal(vsts_name, pod.metadata.name->0) is Some && get_ordinal(vsts_name, pod.metadata.name->0)->0 >= replicas;
        assert(condemned.to_set() == filtered_pods.filter(condemned_ord_filter).to_set()) by {
            let leq = |p1: PodView, p2: PodView| get_ordinal(vsts_name, p1.metadata.name->0)->0 >= get_ordinal(vsts_name, p2.metadata.name->0)->0;
            assert(condemned == filtered_pods.filter(condemned_ord_filter).sort_by(leq));
            lemma_sort_by_does_not_add_or_delete_elements(filtered_pods.filter(condemned_ord_filter), leq);
        }
        assert forall |i: nat| #![trigger condemned[i as int]] i < condemned.len() implies {
            &&& filtered_pods.contains(condemned[i as int])
            &&& condemned_ord_filter(condemned[i as int])
         } by {
            let condemned_pod = condemned[i as int];
            assert(condemned.contains(condemned_pod));
            assert(filtered_pods.filter(condemned_ord_filter).contains(condemned_pod)) by {
                assert(condemned.to_set().contains(condemned_pod));
                assert(filtered_pods.filter(condemned_ord_filter).contains(condemned_pod));
            }
            seq_filter_contains_implies_seq_contains(filtered_pods, condemned_ord_filter, condemned_pod);
        }
        assert(forall |pod: PodView| #[trigger] condemned.contains(pod) ==> pod.metadata.name is Some);
        // coherence of needed pods
        assert forall |ord: nat| #![trigger needed[ord as int]] ord < needed.len() && needed[ord as int] is Some implies {
            let needed_pod = needed[ord as int]->0;
            let key = ObjectRef {
                kind: Kind::PodKind,
                namespace: vsts.metadata.namespace->0,
                name: needed_pod.metadata.name->0,
            };
            let obj = s.resources()[key];
            &&& needed_pod.object_ref() == key
            &&& needed_pod.metadata.name == Some(pod_name(vsts.metadata.name->0, ord))
            &&& s.resources().contains_key(key)
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        } by {
            assert(get_pod_with_ord(vsts_name, filtered_pods, ord) is Some);
            seq_filter_contains_implies_seq_contains(filtered_pods, pod_has_ord(vsts_name, ord), needed[ord as int]->0);
        }
        // no negative sample of uncaptured condemned pods or needed pods, prove by contradiction
        assert forall |ord: nat| ord >= vsts.spec.replicas.unwrap_or(1) implies {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            s.resources().contains_key(key)
                ==> exists |pod: PodView| #[trigger] condemned.contains(pod) && pod.object_ref() == key
        } by {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            if s.resources().contains_key(key) {
                let obj = s.resources()[key];
                let owner_ref_filter = |obj: DynamicObjectView| obj.metadata.owner_references_contains(vsts.controller_owner_ref());
                let filtered_resp_objs = objs.filter(owner_ref_filter);
                get_ordinal_eq_pod_name(vsts_name, ord, key.name);
                // prove that object can pass through all filters
                assert(helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_labels(vsts)(s));
                assert({
                    &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
                    &&& vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
                }); // by all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_labels
                assert(s.resources().values().filter(valid_owned_object_filter(vsts)).contains(obj));
                assert(s.resources().values().filter(valid_owned_object_filter(vsts)).map(|obj: DynamicObjectView| obj.object_ref()).contains(key));
                assert(filtered_resp_objs.to_set().map(|obj: DynamicObjectView| obj.object_ref()).contains(key));
                assert(get_ordinal(vsts_name, key.name) == Some(ord));
                assert(exists |obj: DynamicObjectView| #[trigger] filtered_resp_objs.contains(obj) && obj.object_ref() == key);
                let condemned_obj = choose |obj: DynamicObjectView| #[trigger] filtered_resp_objs.contains(obj) && obj.object_ref() == key;
                seq_filter_contains_implies_seq_contains(objs, owner_ref_filter, condemned_obj);
                let condemned_pod = PodView::unmarshal(condemned_obj)->Ok_0;
                PodView::marshal_preserves_metadata();
                assert(condemned_pod.object_ref() == key);
                assert(filtered_pods.contains(condemned_pod)) by {
                    assert(pods.contains(condemned_pod)) by {
                        let i = choose |i: int| 0 <= i < objs.len() && objs[i] == condemned_obj;
                        assert(PodView::unmarshal(objs[i]) is Ok);
                        assert(pods[i] == condemned_pod);
                        assert(pods.contains(pods[i]));
                    }
                    seq_filter_contains_implies_seq_contains(pods, pod_filter(vsts), condemned_pod);
                }
                assert(condemned.contains(condemned_pod) && condemned_pod.object_ref() == key) by {
                    assert(filtered_pods.filter(condemned_ord_filter).contains(condemned_pod));
                    assert(condemned.to_set().contains(condemned_pod));
                }
            }
        }
    }
}

/* .. -> GetPVC -> AfterGetPVC -> .. */
pub proof fn lemma_from_get_pvc_to_after_get_pvc(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![GetPVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_pvc_req_in_flight(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_get_pvc_req_to_receive_get_pvc_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat, req_msg: Message, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_pvc_req_in_flight(vsts, controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s),
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_pvc_resp_in_flight(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s_prime),
{
    lemma_get_pvc_request_returns_ok_or_err_response(
        s, s_prime, vsts, cluster, controller_id, req_msg
    );
}

pub proof fn lemma_from_get_pvc_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat, resp_msg: Message, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    resp_msg_is_pending_get_pvc_resp_in_flight(vsts, controller_id, resp_msg)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step_or![SkipPVC, CreatePVC])(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_skip_pvc_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![SkipPVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s),
ensures
    pvc_index + 1 < pvc_cnt(vsts)
        ==> at_vsts_step(vsts, controller_id, at_step![GetPVC])(s_prime),
    pvc_index + 1 >= pvc_cnt(vsts)
        ==> at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, (pvc_index + 1) as nat, needed_index, nat0!(), condemned_len)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    if local_state.pvc_index + 1 < local_state.pvcs.len() {} else if local_state.needed_index < local_state.needed.len() {}
}

pub proof fn lemma_from_create_pvc_to_after_create_pvc(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![CreatePVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_create_pvc_req_in_flight(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, (pvc_index + 1) as nat, needed_index, nat0!(), condemned_len)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_create_pvc_req_to_receive_create_pvc_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat, req_msg: Message, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_create_pvc_req_in_flight(vsts, controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s),
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_create_pvc_resp_msg_in_flight_and_created_pvc_exists(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s_prime),
{
    lemma_create_pvc_request_returns_ok_or_already_exists_err_response(
        s, s_prime, vsts, cluster, controller_id, req_msg
    );
}

/* .. -> SkipPVC/AfterCreatePVC -> .. */
// handle_after_create_or_skip_pvc_helper slows down the reasoning
pub proof fn lemma_from_after_create_pvc_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step_or![AfterCreatePVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_create_pvc_resp_msg_in_flight_and_created_pvc_exists(vsts, controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s),
    pvc_index <= pvc_cnt(vsts),
ensures
    at_vsts_step(vsts, controller_id, at_step_or![GetPVC, CreateNeeded, UpdateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_index, needed_index, nat0!(), condemned_len)(s_prime),
    pvc_index < pvc_cnt(vsts)
        ==> at_vsts_step(vsts, controller_id, at_step![GetPVC])(s_prime),
    pvc_index == pvc_cnt(vsts)
        ==> at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded])(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    if local_state.pvc_index < local_state.pvcs.len() {} else if local_state.needed_index < local_state.needed.len() {}
}

/* .. -> CreateNeeded -> AfterCreateNeeded -> .. */
pub proof fn lemma_from_create_needed_to_after_create_needed(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![CreateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_create_needed_pod_req_in_flight(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index + nat1!(), nat0!(), condemned_len)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

// TODO: anyway to increase proof automation by change the way to invoke get_ordinal_eq_pod_name?
pub proof fn lemma_from_after_send_create_needed_pod_req_to_receive_create_needed_pod_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_create_needed_pod_req_in_flight(vsts, controller_id)(s),
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_create_needed_pod_resp_in_flight_and_created_pod_exists(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)(s_prime),
{
    lemma_create_needed_pod_request_returns_ok_response(
        s, s_prime, vsts, cluster, controller_id, req_msg
    );
    let replicas = vsts.spec.replicas.unwrap_or(1) as nat;
    let req = req_msg.content.get_create_request();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    // prove that creation will not affect coherence of condemned pods
    assert(local_state_is_coherent_with_etcd(vsts, next_local_state)(s_prime)) by {
        // 2.a. all pods to be condemned in etcd are captured in next_local_state.condemned
        assert forall |ord: nat| ord >= replicas implies {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            s_prime.resources().contains_key(key)
                ==> exists |pod: PodView| #[trigger] next_local_state.condemned.contains(pod) && pod.object_ref() == key
        } by {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            // created obj shouldn't be considered as condemned
            if !s.resources().contains_key(key) && key == req.key() {
                get_ordinal_eq_pod_name(vsts.metadata.name->0, ord, key.name);
                get_ordinal_eq_pod_name(vsts.metadata.name->0, (next_local_state.needed_index - 1) as nat, key.name);
                assert(false);
            }
        }
        // 2.b. all pods before condemned_index are deleted
        assert forall |i: nat| #![trigger next_local_state.condemned[i as int]] i < next_local_state.condemned_index implies {
            let key = next_local_state.condemned[i as int].object_ref();
            &&& !s_prime.resources().contains_key(key)
        } by {
            let condemned_pod = next_local_state.condemned[i as int];
            if req.key() == condemned_pod.object_ref() {
                let ord = get_ordinal(vsts.metadata.name->0, condemned_pod.metadata.name->0)->0;
                assert(ord >= replicas);
                get_ordinal_eq_pod_name(vsts.metadata.name->0, ord, req.key().name);
                get_ordinal_eq_pod_name(vsts.metadata.name->0, (next_local_state.needed_index - 1) as nat, req.key().name);
                assert(false);
            }
        }
    }
}

pub proof fn lemma_from_create_needed_pod_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, resp_msg: Message, needed_index: nat, condemned_len: nat
)
requires
    resp_msg_or_none(s, vsts.object_ref(), controller_id) is Some,
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    resp_msg_is_pending_create_needed_pod_resp_in_flight_and_created_pod_exists(vsts, controller_id, resp_msg)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)(s),
ensures
    after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

/* .. -> UpdateNeeded -> AfterUpdateNeeded -> .. */
pub proof fn lemma_from_update_needed_to_after_update_needed(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![UpdateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_then_update_needed_pod_req_in_flight(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index + nat1!(), nat0!(), condemned_len)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_get_then_update_needed_pod_req_to_receive_get_then_update_needed_pod_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_then_update_needed_pod_req_in_flight(vsts, controller_id)(s),
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_then_update_needed_pod_resp_in_flight(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)(s_prime),
{
    lemma_get_then_update_needed_pod_request_returns_ok_response(
        s, s_prime, vsts, cluster, controller_id, req_msg
    );
}

pub proof fn lemma_from_get_then_update_needed_pod_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, resp_msg: Message, needed_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    resp_msg_is_pending_get_then_update_needed_pod_resp_in_flight(vsts, controller_id, resp_msg)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), needed_index, nat0!(), condemned_len)(s),
ensures
    after_handle_after_create_or_after_update_needed_helper(vsts, controller_id, needed_index, condemned_len)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_delete_condemned_to_after_delete_condemned(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, condemned_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![DeleteCondemned])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_then_delete_condemned_pod_req_in_flight(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index + 1, condemned_len)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_get_then_delete_condemned_pod_req_to_receive_get_then_delete_condemned_pod_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message, condemned_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_then_delete_condemned_pod_req_in_flight(vsts, controller_id)(s),
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)(s_prime),
{
    let req_msg = req_msg_or_none(s, vsts.object_ref(), controller_id).unwrap();
    lemma_get_then_delete_pod_request_returns_ok_or_not_found_err(
        s, s_prime, vsts, cluster, controller_id, req_msg
    );
    // prove that deletion will not affect coherence of needed pods
    let req = req_msg.content.get_get_then_delete_request();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    assert(local_state_is_coherent_with_etcd(vsts, next_local_state)(s_prime)) by {
        // 1.a. all needed pods in etcd are captured in next_local_state.needed
        assert forall |ord: nat| #![trigger next_local_state.needed[ord as int]] {
            &&& ord < next_local_state.needed.len()
            &&& next_local_state.needed[ord as int] is Some || ord < next_local_state.needed_index
        } implies {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s_prime.resources()[key];
            &&& s_prime.resources().contains_key(key)
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
            // TODO: cover pod updates
        } by {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            if !s_prime.resources().contains_key(key) {
                if req.key() == key {
                    get_ordinal_eq_pod_name(vsts.metadata.name->0, ord, key.name);
                    get_ordinal_eq_pod_name(vsts.metadata.name->0, (next_local_state.needed_index - 1) as nat, key.name);
                    assert(false);
                } else {
                    assert(!s.resources().contains_key(key));
                    assert(false);
                }
            }
        }
    }
}

pub proof fn lemma_from_after_delete_condemned_to_delete_condemned_or_outdated(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, resp_msg: Message, condemned_index: nat, condemned_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    resp_msg_is_pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(vsts, controller_id, resp_msg)(s),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)(s),
    condemned_index <= condemned_len,
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
    pvc_needed_condemned_index_and_condemned_len_are(vsts, controller_id, pvc_cnt(vsts), replicas(vsts), condemned_index, condemned_len)(s_prime),
    condemned_index < condemned_len
        ==> at_vsts_step(vsts, controller_id, at_step![DeleteCondemned])(s_prime),
    condemned_index >= condemned_len
        ==> at_vsts_step(vsts, controller_id, at_step![DeleteOutdated])(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_delete_outdated_to_after_delete_outdated(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![DeleteOutdated])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step_or![AfterDeleteOutdated, Done])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    lift_local(controller_id, vsts, at_step![AfterDeleteOutdated])(s_prime) ==>
        pending_get_then_delete_outdated_pod_req_in_flight(vsts, controller_id)(s_prime),
    lift_local(controller_id, vsts, at_step![Done])(s_prime) ==>
        no_pending_req_in_cluster(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let triggering_cr = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).unwrap();
    let outdated_pods = local_state.needed.filter(outdated_pod_filter(triggering_cr));
    assert(next_local_state == handle_delete_outdated(triggering_cr, None, local_state).0);
    assert forall |pod_or_none: Option<PodView>| #[trigger] outdated_pods.contains(pod_or_none)
        && pod_or_none is Some implies pod_or_none->0.metadata.name is Some by {
        seq_filter_contains_implies_seq_contains(local_state.needed, outdated_pod_filter(triggering_cr), pod_or_none);
    }
    if let Some(pod) = get_largest_unmatched_pods(triggering_cr, local_state.needed) {
        assert(outdated_pods.contains(Some(pod))); // trigger
        assert(get_largest_unmatched_pods(triggering_cr, next_local_state.needed) ==
            get_largest_unmatched_pods(vsts, next_local_state.needed)) by {
            same_filter_implies_same_result(next_local_state.needed, outdated_pod_filter(triggering_cr), outdated_pod_filter(vsts));
        }
    }
}

pub proof fn lemma_from_after_send_get_then_delete_outdated_pod_req_to_receive_get_then_delete_outdated_pod_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteOutdated])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_then_delete_outdated_pod_req_in_flight(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteOutdated])(s_prime),
    pending_get_then_delete_outdated_pod_resp_in_flight_and_outdated_pod_is_deleted(vsts, controller_id)(s_prime),
{
    lemma_get_then_delete_pod_request_returns_ok_or_not_found_err(
        s, s_prime, vsts, cluster, controller_id, req_msg_or_none(s, vsts.object_ref(), controller_id)->0
    );
    VStatefulSetReconcileState::marshal_preserves_integrity();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let victim_pod = get_largest_unmatched_pods(vsts, local_state.needed)->0;
    let victim_ord = get_ordinal(vsts.metadata.name->0, victim_pod.metadata.name->0)->0;
    let req = req_msg_or_none(s, vsts.object_ref(), controller_id)->0.content.get_get_then_delete_request();
    // prove that deletion will not affect coherence of other needed pods
    assert(local_state_is_coherent_with_etcd(vsts, next_local_state)(s_prime)) by {
        assert forall |ord: nat| #![trigger next_local_state.needed[ord as int]] {
            &&& ord < next_local_state.needed.len()
            &&& next_local_state.needed[ord as int] is Some || ord < next_local_state.needed_index
            &&& ord != victim_ord
        } implies {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s_prime.resources()[key];
            &&& s_prime.resources().contains_key(key)
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        } by {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            if !s_prime.resources().contains_key(key) && req.key() == key {
                get_ordinal_eq_pod_name(vsts.metadata.name->0, ord, key.name);
                get_ordinal_eq_pod_name(vsts.metadata.name->0, victim_ord, key.name);
                assert(false);
            }
        }
    }
}

pub proof fn lemma_from_after_delete_outdated_to_done(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteOutdated])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_then_delete_outdated_pod_resp_in_flight_and_outdated_pod_is_deleted(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step![Done])(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

}