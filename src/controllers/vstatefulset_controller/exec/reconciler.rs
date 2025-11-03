use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::trusted::exec_types::VStatefulSet;
use crate::vstd_ext::{seq_lib::*, string_map::StringMap};
use crate::{
    vstatefulset_controller::model::reconciler as model_reconciler,
    vstatefulset_controller::trusted::reconciler as trusted_reconciler,
    vstd_ext::string_view::i32_to_string,
};
use std::collections::BTreeSet;
use vstd::{prelude::*, seq_lib::*};

verus! {

    pub fn filter_pods(pods: Vec<Pod>, vsts: VStatefulSet) -> (filtered: Vec<Pod>)
        requires vsts@.well_formed()
        ensures filtered.deep_view() =~= model_reconciler::filter_pods(pods.deep_view(), vsts@)
    {

        let mut filtered_pods = Vec::new();

        proof {
            assert_seqs_equal!(filtered_pods.deep_view(), model_reconciler::filter_pods(pods.deep_view().take(0), vsts@));
        }

        let mut idx = 0;
        for idx in 0..pods.len()
            invariant
                idx <= pods.len(),
                filtered_pods.deep_view()
                    == model_reconciler::filter_pods(pods.deep_view().take(idx as int), vsts@),
        {
            let pod = &pods[idx];
            if  pod.metadata().owner_references_contains(&vsts.controller_owner_ref())
                && vsts.spec().selector().matches(pod.metadata().labels().unwrap_or(StringMap::empty()))
                && vsts.metadata().name().is_some()
                && trusted_reconciler::get_ordinal(vsts.metadata().name().unwrap(), &pod).is_some() {
                filtered_pods.push(pod.clone());
            }

            // prove the invariant
            proof {
                let spec_filter = |pod: PodView|
                    pod.metadata.owner_references_contains(vsts@.controller_owner_ref())
                    && vsts@.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::<Seq<char>, Seq<char>>::empty()))
                    && vsts@.metadata.name is Some
                    && model_reconciler::get_ordinal(vsts@.metadata.name->0, pod) is Some;

                let old_filtered = if spec_filter(pod@) {
                    filtered_pods.deep_view().drop_last()
                } else {
                    filtered_pods.deep_view()
                };

                assert(old_filtered == pods.deep_view().take(idx as int).filter(spec_filter));
                lemma_filter_push(pods.deep_view().take(idx as int), spec_filter, pod@);
                assert(pods.deep_view().take(idx as int).push(pod@)
                    == pods.deep_view().take((idx + 1) as int));
                assert(spec_filter(pod@) ==> filtered_pods.deep_view() == old_filtered.push(pod@));
            }

        }
        assert(pods.deep_view() == pods.deep_view().take(pods.len() as int));
        filtered_pods
    }

    pub fn pod_name(parent_name: String, ordinal: i32) -> (result: String)
        requires ordinal >= 0
        ensures result@ == model_reconciler::pod_name(parent_name@, ordinal as nat)
    {
        parent_name
        .concat("-")
        .concat(i32_to_string(ordinal).as_str())
    }

    pub fn pvc_name(pvc_template_name: String, vsts_name: String, ordinal: i32) -> (result: String)
        requires ordinal >= 0
        ensures result@ == model_reconciler::pvc_name(pvc_template_name@, vsts_name@, ordinal as nat)
    {
        pvc_template_name
        .concat("-")
        .concat(pod_name(vsts_name, ordinal).as_str())
    }

}
