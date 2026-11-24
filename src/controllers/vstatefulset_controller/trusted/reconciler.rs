use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::seq_lib::*;
use crate::vstd_ext::string_view::*;
use crate::{
    vstatefulset_controller::model::reconciler as model_reconciler,
    vstatefulset_controller::trusted::liveness_theorem as liveness_theorem,
};
use vstd::{prelude::*, vstd::string::*, utf8::*};

verus! {

    pub fn has_ordinal(parent_name: &String, pod_name: &String) -> (res: bool)
        requires is_ascii_chars(parent_name@),
        ensures
            res == (model_reconciler::get_ordinal(parent_name@, pod_name@) is Some),
    {
        get_ordinal_suffix(parent_name, pod_name).is_some()
    }

    // A pod name is "vstatefulset-" + parent_name + "-" + ordinal, so getting the ordinal is
    // stripping that prefix and parsing the rest. parent_name is ascii (its metadata is
    // well formed), which lets us index by byte.
    pub fn get_ordinal(parent_name: &String, pod_name: &String) -> (ordinal: Option<usize>)
        requires is_ascii_chars(parent_name@),
        ensures
            match ordinal {
                Some(ord) => model_reconciler::get_ordinal(parent_name@, pod_name@) == Some(ord as nat),
                None => match model_reconciler::get_ordinal(parent_name@, pod_name@) {
                    None => true,
                    Some(ord) => ord > usize::MAX as nat,
                },
            },
    {
        broadcast use vstd::string::group_string_axioms, vstd::utf8::is_ascii_chars_concat, vstd::slice::group_slice_axioms;
        proof {
            reveal(model_reconciler::get_ordinal);
            reveal_strlit("vstatefulset");
            reveal_strlit("-");
        }
        // we don't have executable CustomResource kind, hardcoded as a temporary solution
        let prefix = "vstatefulset".to_string().concat("-").concat(parent_name.as_str()).concat("-");
        assert forall |ord: nat| #[trigger] liveness_theorem::pod_name(parent_name@, ord)
            == prefix@ + int_to_string_view(ord as int) by {
            assert(liveness_theorem::pod_name(parent_name@, ord) =~= prefix@ + int_to_string_view(ord as int));
        }
        // a pod name carrying an ordinal is ascii, since the prefix and the ordinal are
        let prefix_str = prefix.as_str();
        let pod_str = pod_name.as_str();
        if !pod_str.is_ascii() {
            assert forall |ord: nat| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord) by {
                int_to_string_view_ascii();
            }
            return None;
        }
        // the byte length is the character length because both strings are ascii
        assert(vstd::string::is_ascii(prefix_str));
        let prefix_len = prefix_str.as_bytes().len();
        let name_len = pod_str.as_bytes().len();
        assert(prefix_len == prefix@.len());
        assert(name_len == pod_name@.len());
        if name_len < prefix_len {
            assert forall |ord: nat| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord) by {
                assert((prefix@ + int_to_string_view(ord as int)).len() >= prefix@.len());
            }
            return None;
        }
        let head = pod_str.substring_ascii(0, prefix_len);
        let tail = pod_str.substring_ascii(prefix_len, name_len);
        assert(pod_name@ =~= head@ + tail@);
        if !string_equal(&prefix, head) {
            assert forall |ord: nat| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord) by {
                assert((prefix@ + int_to_string_view(ord as int)).subrange(0, prefix_len as int) =~= prefix@);
                assert(pod_name@.subrange(0, prefix_len as int) =~= head@);
            }
            return None;
        }
        let ordinal = parse_usize(tail);
        match ordinal {
            Some(v) => {
                assert(pod_name@ == liveness_theorem::pod_name(parent_name@, v as nat));
                let ghost chosen = choose |ord: nat| pod_name@ == liveness_theorem::pod_name(parent_name@, ord);
                assert(chosen == v) by {
                    seq_equal_preserved_by_add_prefix(prefix@, int_to_string_view(chosen as int), int_to_string_view(v as int));
                    int_to_string_view_injectivity();
                }
            },
            None => {
                assert forall |ord: usize| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord as nat) by {
                    if pod_name@ == liveness_theorem::pod_name(parent_name@, ord as nat) {
                        seq_equal_preserved_by_add_prefix(prefix@, tail@, int_to_string_view(ord as int));
                    }
                }
                proof {
                    if let Some(chosen) = model_reconciler::get_ordinal(parent_name@, pod_name@) {
                        if chosen <= usize::MAX as nat {
                            let u = chosen as usize;
                            assert(pod_name@ == liveness_theorem::pod_name(parent_name@, u as nat));
                        }
                    }
                }
            },
        }
        ordinal
    }

    // The decimal suffix of a pod name that carries an ordinal of parent_name, i.e., the part
    // after "vstatefulset-" + parent_name + "-". Unlike get_ordinal, it does not bound the
    // ordinal by usize::MAX.
    pub fn get_ordinal_suffix<'a>(parent_name: &String, pod_name: &'a String) -> (res: Option<&'a str>)
        requires is_ascii_chars(parent_name@),
        ensures
            match res {
                Some(tail) => is_canonical_decimal_bytes(tail.spec_bytes())
                    && model_reconciler::get_ordinal(parent_name@, pod_name@) == Some(decimal_bytes_val(tail.spec_bytes())),
                None => model_reconciler::get_ordinal(parent_name@, pod_name@) is None,
            },
    {
        broadcast use vstd::string::group_string_axioms, vstd::utf8::is_ascii_chars_concat, vstd::slice::group_slice_axioms;
        proof {
            reveal(model_reconciler::get_ordinal);
            reveal_strlit("vstatefulset");
            reveal_strlit("-");
        }
        let prefix = "vstatefulset".to_string().concat("-").concat(parent_name.as_str()).concat("-");
        assert forall |ord: nat| #[trigger] liveness_theorem::pod_name(parent_name@, ord)
            == prefix@ + int_to_string_view(ord as int) by {
            assert(liveness_theorem::pod_name(parent_name@, ord) =~= prefix@ + int_to_string_view(ord as int));
        }
        let prefix_str = prefix.as_str();
        let pod_str = pod_name.as_str();
        if !pod_str.is_ascii() {
            assert forall |ord: nat| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord) by {
                int_to_string_view_ascii();
            }
            return None;
        }
        assert(vstd::string::is_ascii(prefix_str));
        let prefix_len = prefix_str.as_bytes().len();
        let name_len = pod_str.as_bytes().len();
        assert(prefix_len == prefix@.len());
        assert(name_len == pod_name@.len());
        if name_len < prefix_len {
            assert forall |ord: nat| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord) by {
                assert((prefix@ + int_to_string_view(ord as int)).len() >= prefix@.len());
            }
            return None;
        }
        let head = pod_str.substring_ascii(0, prefix_len);
        let tail = pod_str.substring_ascii(prefix_len, name_len);
        assert(pod_name@ =~= head@ + tail@);
        if !string_equal(&prefix, head) {
            assert forall |ord: nat| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord) by {
                assert((prefix@ + int_to_string_view(ord as int)).subrange(0, prefix_len as int) =~= prefix@);
                assert(pod_name@.subrange(0, prefix_len as int) =~= head@);
            }
            return None;
        }
        if !is_canonical_decimal_nat(tail) {
            assert forall |ord: nat| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord) by {
                if pod_name@ == liveness_theorem::pod_name(parent_name@, ord) {
                    seq_equal_preserved_by_add_prefix(prefix@, tail@, int_to_string_view(ord as int));
                }
            }
            return None;
        }
        proof {
            let ord = choose |i: nat| tail@ == #[trigger] int_to_string_view(i as int);
            assert(pod_name@ == liveness_theorem::pod_name(parent_name@, ord));
            let chosen = choose |o: nat| pod_name@ == liveness_theorem::pod_name(parent_name@, o);
            seq_equal_preserved_by_add_prefix(prefix@, int_to_string_view(chosen as int), int_to_string_view(ord as int));
            int_to_string_view_injectivity();
            assert(chosen == ord);
            lemma_nat_to_string_view_props(ord);
            lemma_nat_str_to_canonical_bytes(ord);
            vstd::string::is_ascii_spec_bytes(tail);
            assert(tail.spec_bytes() =~= Seq::new(tail@.len(), |k: int| tail@[k] as u8));
        }
        Some(tail)
    }

    // The order cmp_ordinal_suffix_desc gives two ordinals: the larger ordinal comes first.
    pub open spec fn ordinal_cmp_desc(a: nat, b: nat) -> std::cmp::Ordering {
        if a > b {
            std::cmp::Ordering::Less
        } else if a < b {
            std::cmp::Ordering::Greater
        } else {
            std::cmp::Ordering::Equal
        }
    }

    // Compares two canonical decimal suffixes by the ordinals they denote, larger first, without
    // parsing them (they may be larger than usize::MAX): a longer suffix is a larger ordinal, and
    // suffixes of the same length compare digit by digit.
    pub fn cmp_ordinal_suffix_desc(s1: &str, s2: &str) -> (res: std::cmp::Ordering)
        requires
            is_canonical_decimal_bytes(s1.spec_bytes()),
            is_canonical_decimal_bytes(s2.spec_bytes()),
        ensures
            res == ordinal_cmp_desc(decimal_bytes_val(s1.spec_bytes()), decimal_bytes_val(s2.spec_bytes())),
    {
        let b1 = s1.as_bytes();
        let b2 = s2.as_bytes();
        if b2.len() < b1.len() {
            proof { lemma_decimal_bytes_len_lt(b2@, b1@); }
            return std::cmp::Ordering::Less;
        }
        if b2.len() > b1.len() {
            proof { lemma_decimal_bytes_len_lt(b1@, b2@); }
            return std::cmp::Ordering::Greater;
        }
        let mut i: usize = 0;
        while i < b1.len()
            invariant
                b1@ == s1.spec_bytes(),
                b2@ == s2.spec_bytes(),
                b1@.len() == b2@.len(),
                is_canonical_decimal_bytes(b1@),
                is_canonical_decimal_bytes(b2@),
                0 <= i <= b1@.len(),
                forall |j: int| 0 <= j < i ==> b1@[j] == b2@[j],
            decreases b1@.len() - i,
        {
            if b2[i] < b1[i] {
                proof { lemma_decimal_bytes_same_len_lt(b2@, b1@, i as int); }
                return std::cmp::Ordering::Less;
            }
            if b2[i] > b1[i] {
                proof { lemma_decimal_bytes_same_len_lt(b1@, b2@, i as int); }
                return std::cmp::Ordering::Greater;
            }
            i += 1;
        }
        proof { assert(b1@ =~= b2@); }
        std::cmp::Ordering::Equal
    }

    // Verus gap: vstd specifies `<[T]>::sort_by` only as a sorted permutation, without its
    // stability, and `Seq::sort_by` is closed (see lemma_sort_by_does_not_add_or_delete_elements),
    // so the equality below cannot be proved. The comparator is the verified pair
    // get_ordinal_suffix / cmp_ordinal_suffix_desc, which orders pods carrying an ordinal by
    // decreasing ordinal (including ordinals above usize::MAX), as the spec's leq does; both
    // std's sort_by and the spec's merge sort are stable.
    #[verifier(external_body)]
    pub fn sort_pods_by_ord(parent_name: &String, pods: &mut Vec<Pod>)
        requires
            is_ascii_chars(parent_name@),
            forall |i: int| #![trigger old(pods)@[i]] 0 <= i < old(pods)@.len() ==> {
                &&& old(pods)@[i]@.metadata.name is Some
                &&& model_reconciler::get_ordinal(parent_name@, old(pods)@[i]@.metadata.name->0) is Some
            },
        ensures final(pods).deep_view() == old(pods).deep_view().sort_by(|p1: PodView, p2: PodView| model_reconciler::get_ordinal(parent_name@, p1.metadata.name->0)->0 >= model_reconciler::get_ordinal(parent_name@, p2.metadata.name->0)->0)
    {
        pods.sort_by(|p1: &Pod, p2: &Pod| {
            let n1 = p1.metadata().name().unwrap();
            let n2 = p2.metadata().name().unwrap();
            match (
                get_ordinal_suffix(parent_name, &n1),
                get_ordinal_suffix(parent_name, &n2),
            ) {
                (Some(s1), Some(s2)) => cmp_ordinal_suffix_desc(s1, s2),
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, Some(_)) => std::cmp::Ordering::Greater,
                (None, None) => std::cmp::Ordering::Equal,
            }
        });
    }
}
