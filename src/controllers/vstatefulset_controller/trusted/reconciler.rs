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
use vstd::prelude::*;
use vstd::utf8::is_ascii_chars;
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

    // The pod name of a vstatefulset is "vstatefulset-" + parent_name + "-" + ordinal,
    // so getting the ordinal is stripping that prefix and parsing the rest.
    // parent_name is ascii (guaranteed by state_validation), which lets us index by byte.
    pub fn get_ordinal(parent_name: &String, pod_name: &String) -> (ordinal: Option<usize>)
        requires is_ascii_chars(parent_name@),
        ensures (
            (ordinal@ matches Some(v1) && model_reconciler::get_ordinal(parent_name@, pod_name@) matches Some(v2) && v1 == v2)
            || (ordinal@ matches None && model_reconciler::get_ordinal(parent_name@, pod_name@) matches None)
        )
    {
        broadcast use vstd::string::group_string_axioms, vstd::utf8::is_ascii_chars_concat, vstd::slice::group_slice_axioms;
        proof {
            reveal_strlit("vstatefulset");
            reveal_strlit("-");
        }
        // we don't have executable CustomResource kind, hardcoded as a temporary solution
        let prefix = "vstatefulset".to_string().concat("-").concat(parent_name.as_str()).concat("-");
        assert forall |ord: nat| #[trigger] liveness_theorem::pod_name(parent_name@, ord)
            == prefix@ + int_to_string_view(ord as int) by {
            assert(liveness_theorem::pod_name(parent_name@, ord) =~= prefix@ + int_to_string_view(ord as int));
        }
        // every pod name that carries an ordinal is ascii, because both the prefix and the
        // decimal representation of the ordinal are
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
                assert forall |ord: nat| pod_name@ != #[trigger] liveness_theorem::pod_name(parent_name@, ord) by {
                    if pod_name@ == liveness_theorem::pod_name(parent_name@, ord) {
                        seq_equal_preserved_by_add_prefix(prefix@, tail@, int_to_string_view(ord as int));
                    }
                }
            },
        }
        ordinal
    }

    // TODO: verify this function
    #[verifier(external_body)]
    pub fn sort_pods_by_ord(parent_name: &String, pods: &mut Vec<Pod>) 
        requires is_ascii_chars(parent_name@),
        ensures final(pods).deep_view() == old(pods).deep_view().sort_by(|p1: PodView, p2: PodView| model_reconciler::get_ordinal(parent_name@, p1.metadata.name->0)->0 >= model_reconciler::get_ordinal(parent_name@, p2.metadata.name->0)->0)
    {
        pods.sort_by(|p1: &Pod, p2: &Pod| get_ordinal(parent_name, &p2.metadata().name().unwrap()).cmp(&get_ordinal(parent_name, &p1.metadata().name().unwrap())));
    }
}
