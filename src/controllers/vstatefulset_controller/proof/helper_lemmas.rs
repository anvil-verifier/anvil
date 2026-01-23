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

#[verifier(external_body)]
pub proof fn pvc_name_with_vsts_match_vsts(
    name: StringView, vsts: VStatefulSetView
)
requires
    // index, ord
    exists |i: (nat, nat)| name == #[trigger]
        pvc_name(vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0, vsts.metadata.name->0, i.1),
ensures
    pvc_name_match(name, vsts.metadata.name->0),
{}
}
