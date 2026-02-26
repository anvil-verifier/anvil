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

// helper lemmas about pvc_name_match
// NOTE: dash_char_view_eq_str_view may be helpful
#[verifier(external_body)]
pub proof fn vsts_name_non_eq_implies_no_pvc_name_match(
    name: StringView, vsts_name_a: StringView, vsts_name_b: StringView
)
requires
    vsts_name_a != vsts_name_b,
    pvc_name_match(name, vsts_name_a),
ensures
    !pvc_name_match(name, vsts_name_b),
{}

#[verifier(external_body)]
pub proof fn vsts_name_non_eq_implies_no_pod_name_match(
    name: StringView, vsts_name_a: StringView, vsts_name_b: StringView
)
requires
    vsts_name_a != vsts_name_b,
    pod_name_match(name, vsts_name_a),
ensures
    !pod_name_match(name, vsts_name_b),
{}

// helper lemmas about name prefixes
#[verifier(external_body)]
pub proof fn generated_name_has_vsts_prefix_implies_generate_name_field_has_vsts_prefix(
    name: StringView, generate_name_field: StringView, generated_suffix: StringView
)
requires
    has_vsts_prefix(name),
    name == generate_name_field + generated_suffix,
    dash_free(generated_suffix),
ensures
    has_vsts_prefix(generate_name_field),
{
    let vsts_prefix = VStatefulSetView::kind()->CustomResourceKind_0 + "-"@;
    dash_char_view_eq_str_view();
    assert(!dash_free(name)) by {
        assert(name[vsts_prefix.len() - 1] == '-'@);
    }
    assert(!dash_free(generate_name_field)) by {
        if dash_free(generate_name_field) {
            assert(dash_free(name));
            assert(false);
        }
    }
    // we know exists |suffix| name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + suffix from has_vsts_prefix(name)
    // and name == generate_name_field + generated_suffix, dash_free(generated_suffix)
    // so generate_name_field must also start with VStatefulSetView::kind()->CustomResourceKind_0 + "-"@
    // yet the proof is hard
}

#[verifier(external_body)]
pub proof fn no_vsts_prefix_implies_no_vsts_previx_in_generate_name_field(s: APIServerState, generate_name_field: StringView)
requires
    !has_vsts_prefix(generate_name_field),
ensures
    !has_vsts_prefix(generated_name(s, generate_name_field))
{}

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

#[verifier(external_body)]
pub proof fn no_vsts_prefix_implies_no_pod_name_match(name: StringView)
requires
    !has_vsts_prefix(name),
ensures
    forall |vsts: VStatefulSetView| #![trigger vsts.metadata.name->0]
        !pod_name_match(name, vsts.metadata.name->0),
{}

}
