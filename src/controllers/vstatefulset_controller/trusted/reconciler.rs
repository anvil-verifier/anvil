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
            return false;
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
            return false;
        }
        let head = pod_str.substring_ascii(0, prefix_len);
        let tail = pod_str.substring_ascii(prefix_len, name_len);
        assert(pod_name@ =~= head@ + tail@);
        if !string_equal(&prefix, head) {
            assert forall |ord: nat| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord) by {
                assert((prefix@ + int_to_string_view(ord as int)).subrange(0, prefix_len as int) =~= prefix@);
                assert(pod_name@.subrange(0, prefix_len as int) =~= head@);
            }
            return false;
        }
        let valid = is_canonical_decimal_nat(tail);
        proof {
            if valid {
                let ord = choose |i: nat| tail@ == #[trigger] int_to_string_view(i as int);
                assert(pod_name@ == liveness_theorem::pod_name(parent_name@, ord));
            } else {
                assert forall |ord: nat| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord) by {
                    if pod_name@ == liveness_theorem::pod_name(parent_name@, ord) {
                        seq_equal_preserved_by_add_prefix(prefix@, tail@, int_to_string_view(ord as int));
                    }
                }
            }
        }
        valid
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

    #[verifier::external]
    pub fn get_ordinal_suffix<'a>(parent_name: &String, pod_name: &'a String) -> Option<&'a str> {
        let prefix = format!("vstatefulset-{}-", parent_name);
        let tail = pod_name.strip_prefix(prefix.as_str())?;
        if is_canonical_decimal_nat(tail) {
            Some(tail)
        } else {
            None
        }
    }

    #[verifier::external]
    pub fn cmp_ordinal_suffix_desc(s1: &str, s2: &str) -> std::cmp::Ordering {
        s2.len().cmp(&s1.len()).then_with(|| s2.cmp(s1))
    }

    // TODO: verify this function
    #[verifier(external_body)]
    pub fn sort_pods_by_ord(parent_name: &String, pods: &mut Vec<Pod>) 
        requires is_ascii_chars(parent_name@),
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
