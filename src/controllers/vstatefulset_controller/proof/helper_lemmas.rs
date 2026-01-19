use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*,
    api_server::types::*,
    network::state_machine::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_invariants, predicate::*, guarantee::*},
    trusted::{rely::*, spec_types::*,  liveness_theorem::*, step::VStatefulSetReconcileStepView::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*, string_view::*};
use vstd::{seq_lib::*, map_lib::*, set_lib::*};
use vstd::prelude::*;

verus! {

pub open spec fn get_largest_ordinal_of_unmatched_properties(vsts: VStatefulSetView, pods: Seq<Option<PodView>>) -> bool {
    let ordinal = get_largest_ordinal_of_unmatched_pods(vsts, pods);
    ordinal is Some ==> {
        &&& 0 <= ordinal->0 < pods.len()
        &&& pods[ordinal->0 as int] is Some
    }
}

pub proof fn lemma_get_largest_ordinal_of_unmatched_well_behaved(vsts: VStatefulSetView, pods: Seq<Option<PodView>>)
    ensures get_largest_ordinal_of_unmatched_properties(vsts, pods)
{
    let ordinal = get_largest_ordinal_of_unmatched_pods(vsts, pods);
    if ordinal is Some {
        let ordinals = Seq::new(pods.len(), |i: int| i as nat);
        let pred = |ordinal: nat| pods[ordinal as int] is Some && !pod_matches(vsts, pods[ordinal as int]->0);
        let filtered = ordinals.filter(pred);

        assert(filtered.len() > 0);
        assert(ordinal->0 == filtered.last());

        assert(filtered.contains(ordinal->0));
        seq_filter_contains_implies_seq_contains(ordinals, pred, ordinal->0);
        assert(ordinals.contains(ordinal->0));

        assert(0 <= ordinal->0 < pods.len());

        assert(pred(ordinal->0));
        assert(pods[ordinal->0 as int] is Some);
    }
}

pub proof fn get_ordinal_eq_pod_name(vsts_name: StringView, ord: nat, compared_pod_name: StringView)
ensures
    (get_ordinal(vsts_name, compared_pod_name) == Some(ord))
        <==> compared_pod_name == pod_name(vsts_name, ord)
{
    if pod_name(vsts_name, ord) == compared_pod_name {
        assert(get_ordinal(vsts_name, compared_pod_name) is Some);
        if get_ordinal(vsts_name, compared_pod_name) != Some(ord) {
            let havoc_ord = get_ordinal(vsts_name, compared_pod_name)->0;
            assert(pod_name(vsts_name, havoc_ord) == pod_name(vsts_name, ord));
            assert(pod_name(vsts_name, havoc_ord) ==
                VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + vsts_name + "-"@ + int_to_string_view(havoc_ord as int));
            assert(pod_name(vsts_name, ord) ==
                VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + vsts_name + "-"@ + int_to_string_view(ord as int));
            assert(VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + vsts_name + "-"@ + int_to_string_view(havoc_ord as int)
                == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + vsts_name + "-"@ + int_to_string_view(ord as int));
            if int_to_string_view(havoc_ord as int) != int_to_string_view(ord as int) {
                seq_unequal_preserved_by_add_prefix(
                    VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + vsts_name + "-"@,
                    int_to_string_view(havoc_ord as int),
                    int_to_string_view(ord as int)
                );
                assert(false);
            }
            int_to_string_view_injectivity();
            assert(false);
        }
    }
}

// workaround for lemma_pre_leads_to_post_by_api_server with no lifted input
pub proof fn lemma_pre_lead_to_post_by_api_server_handling_request_from_controller(
    cluster: Cluster, spec: TempPred<ClusterState>, next: ActionPred<ClusterState>,
    pre: StatePred<ClusterState>, post: StatePred<ClusterState>, controller_id: int, cr_key: ObjectRef
)
requires
    forall |s, s_prime| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
    forall |s, s_prime| pre(s) && #[trigger] next(s, s_prime) 
        && cluster.api_server_next().forward(s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg)(s, s_prime) ==> post(s_prime),
    forall |s| #[trigger] pre(s) ==> cluster.api_server_action_pre(APIServerStep::HandleRequest, s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg)(s),
    spec.entails(always(lift_action(next))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
ensures spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    let input = |s: ClusterState| s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg;
    // api_server_action_pre_implies_next_pre
    let forward = |i| cluster.api_server_next().forward(i);
    // hack to obtain input on the fly
    assert forall |s| #[trigger] pre(s) implies enabled(forward(input(s)))(s) by {
        cluster.api_server_action_pre_implies_next_pre(
            APIServerStep::HandleRequest, input(s)
        );
        let host_result = cluster.api_server().next_result(
            APIServerActionInput{ recv: input(s) },
            s.api_server
        );
        let msg_ops = MessageOps {
            recv: input(s),
            send: host_result->Enabled_1.send,
        };
        let network_result = network().next_result(msg_ops, s.network);
        let s_prime = ClusterState {
            api_server: host_result->Enabled_0,
            network: network_result->Enabled_0,
            ..s
        };
        assert(forward(input(s))(s, s_prime));
    };
    assert forall |i| #[trigger] cluster.api_server_next().pre(i) =~= enabled(forward(i)) by {
        assert forall |s| #[trigger] cluster.api_server_next().pre(i)(s) == enabled(forward(i))(s) by {
            if cluster.api_server_next().pre(i)(s) {
                let host_result = cluster.api_server().next_result(
                    APIServerActionInput{ recv: i },
                    s.api_server
                );
                let msg_ops = MessageOps {
                    recv: i,
                    send: host_result->Enabled_1.send,
                };
                let network_result = network().next_result(msg_ops, s.network);
                let s_prime = ClusterState {
                    api_server: host_result->Enabled_0,
                    network: network_result->Enabled_0,
                    ..s
                };
                assert(forward(i)(s, s_prime));
            }
        };
    };
    assert forall |i| #[trigger] spec.entails(weak_fairness(forward(i))) by {
        use_tla_forall(spec, |i| cluster.api_server_next().weak_fairness(i), i);
        temp_pred_equality(
            weak_fairness(cluster.api_server_next().forward(i)),
            cluster.api_server_next().weak_fairness(i)
        );
    };
    spec_entails_tla_forall(spec, |i| weak_fairness(forward(i)));
    wf1_forall_input(
        spec, next, forward, input, pre, post
    );
}
}
