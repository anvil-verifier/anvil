use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*,
    api_server::{types::*, state_machine::*},
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

// this is simple but introduced a lot of flakiness
pub proof fn pvc_name_match_implies_has_vsts_prefix(name: StringView)
requires
    exists |vsts_name| #[trigger] pvc_name_match(name, vsts_name),
ensures
    has_vsts_prefix(name),
{
    let vsts_name = choose |vsts_name| #[trigger] pvc_name_match(name, vsts_name);
    let i = choose |i: (StringView, nat)| name == #[trigger] pvc_name(i.0, vsts_name, i.1) && dash_free(i.0);
    assert(name == pvc_name(i.0, vsts_name, i.1));
    assert(name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + (i.0 + "-"@ + pod_name_without_vsts_prefix(vsts_name, i.1)));
}

pub proof fn pod_name_match_implies_has_vsts_prefix(name: StringView)
requires
    exists |vsts_name| #[trigger] pod_name_match(name, vsts_name),
ensures
    has_vsts_prefix(name),
{
    let vsts_name = choose |vsts_name| #[trigger] pod_name_match(name, vsts_name);
    let ord = choose |ord: nat| name == pod_name(vsts_name, ord);
    assert(name == pod_name(vsts_name, ord));
    assert(name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + pod_name_without_vsts_prefix(vsts_name, ord));
}

pub proof fn pvc_name_with_vsts_implies_pvc_name_match_vsts(
    name: StringView, vsts: VStatefulSetView
)
requires
    // index, ord
    exists |i: (nat, nat)| name == #[trigger] pvc_name(vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0, vsts.metadata.name->0, i.1)
        && dash_free(vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0),
ensures
    pvc_name_match(name, vsts.metadata.name->0),
{
    let i = choose |i: (nat, nat)| name == #[trigger] pvc_name(vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0, vsts.metadata.name->0, i.1)
        && dash_free(vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0);
    let j = (vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0, i.1);
    assert((|j: (StringView, nat)| name == pvc_name(j.0, vsts.metadata.name->0, j.1))(j));
    assert(pvc_name_match(name, vsts.metadata.name->0));
}

pub proof fn vsts_name_non_eq_implies_no_pvc_name_match(
    name: StringView, vsts_name_a: StringView, vsts_name_b: StringView
)
requires
    vsts_name_a != vsts_name_b,
    pvc_name_match(name, vsts_name_a),
ensures
    !pvc_name_match(name, vsts_name_b),
{
    if pvc_name_match(name, vsts_name_b) {
        let i = choose |i: (StringView, nat)| name == #[trigger] pvc_name(i.0, vsts_name_a, i.1) && dash_free(i.0);
        let suffix = i.0 + "-"@ + pod_name_without_vsts_prefix(vsts_name_a, i.1);
        assert(name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + suffix);
        let j = choose |j: (StringView, nat)| name == #[trigger] pvc_name(j.0, vsts_name_b, j.1) && dash_free(j.0);
        let suffix2 = j.0 + "-"@ + pod_name_without_vsts_prefix(vsts_name_b, j.1);
        assert(name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + suffix2);
        assert(suffix == suffix2) by {
            assert("-"@ + suffix == name.subrange(VStatefulSetView::kind()->CustomResourceKind_0.len() as int, name.len() as int));
            assert("-"@ + suffix2 == name.subrange(VStatefulSetView::kind()->CustomResourceKind_0.len() as int, name.len() as int));
            if suffix != suffix2 {
                seq_unequal_preserved_by_add_prefix(
                    VStatefulSetView::kind()->CustomResourceKind_0 + "-"@,
                    suffix,
                    suffix2
                );
                assert(false);
            }
        }
        assert(pod_name_without_vsts_prefix(vsts_name_a, i.1) != pod_name_without_vsts_prefix(vsts_name_b, j.1)) by {
            int_to_string_view_dash_free();
            lemma_dash_free_suffix_preserves_prefix_inequality(
                vsts_name_a,
                vsts_name_b,
                int_to_string_view(i.1 as int),
                int_to_string_view(j.1 as int)
            );
        }
        lemma_dash_free_prefix_preserves_suffix_inequality(
            i.0, j.0, pod_name_without_vsts_prefix(vsts_name_a, i.1), pod_name_without_vsts_prefix(vsts_name_b, j.1)
        );
        assert(false);
    }
}

pub proof fn vsts_name_non_eq_implies_no_pod_name_match(
    name: StringView, vsts_name_a: StringView, vsts_name_b: StringView
)
requires
    vsts_name_a != vsts_name_b,
    pod_name_match(name, vsts_name_a),
ensures
    !pod_name_match(name, vsts_name_b),
{
    if pod_name_match(name, vsts_name_b) {
        let ord_a = choose |ord_a: nat| name == pod_name(vsts_name_a, ord_a);
        let ord_b = choose |ord_b: nat| name == pod_name(vsts_name_b, ord_b);
        assert(name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + pod_name_without_vsts_prefix(vsts_name_a, ord_a));
        assert(name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + pod_name_without_vsts_prefix(vsts_name_b, ord_b));
        assert(pod_name_without_vsts_prefix(vsts_name_a, ord_a) != pod_name_without_vsts_prefix(vsts_name_b, ord_b)) by {
            int_to_string_view_dash_free();
            lemma_dash_free_suffix_preserves_prefix_inequality(
                vsts_name_a,
                vsts_name_b,
                int_to_string_view(ord_a as int),
                int_to_string_view(ord_b as int)
            );
        }
        seq_equal_preserved_by_add_prefix(
            VStatefulSetView::kind()->CustomResourceKind_0 + "-"@,
            pod_name_without_vsts_prefix(vsts_name_a, ord_a),
            pod_name_without_vsts_prefix(vsts_name_b, ord_b)
        );
        assert(false);
    }
}

// helper lemma
pub proof fn no_vsts_prefix_implies_no_pvc_name_match(name: StringView)
requires
    !has_vsts_prefix(name),
ensures
    forall |vsts_name: StringView| ! #[trigger] pvc_name_match(name, vsts_name),
{
    // proof by contradiction
    if exists |vsts_name: StringView| #[trigger] pvc_name_match(name, vsts_name) {
        let witness_vsts = choose |vsts_name: StringView| #[trigger] pvc_name_match(name, vsts_name);
        let i = choose |i: (StringView, nat)| name == #[trigger] pvc_name(i.0, witness_vsts, i.1);
        let suffix = i.0 + "-"@ + pod_name_without_vsts_prefix(witness_vsts, i.1);
        assert(name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + suffix);
        assert(has_vsts_prefix(name));
    }
}

}
