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

    // copied verbatim from vreplicaset_controller::objects_to_pods 
    // should we refactor to only have one version of this?
    fn objects_to_pods(objs: Vec<DynamicObject>) -> (pods_or_none: Option<Vec<Pod>>)
        ensures pods_or_none.deep_view() == model_reconciler::objects_to_pods(objs.deep_view())
    {
        let mut pods = Vec::new();
        let mut idx = 0;

        proof {
            let model_result = model_reconciler::objects_to_pods(objs.deep_view());
            if model_result.is_some() {
                assert_seqs_equal!(
                    pods.deep_view(),
                    model_result.unwrap().take(0)
                );
            }
        }

        for idx in 0..objs.len()
            invariant
                idx <= objs.len(),
                ({
                    let model_result = model_reconciler::objects_to_pods(objs.deep_view());
                    &&& (model_result.is_some() ==>
                            pods.deep_view() == model_result.unwrap().take(idx as int))
                    &&& forall|i: int| 0 <= i < idx ==> PodView::unmarshal(#[trigger] objs@[i]@).is_ok()
                }),
        {
            let pod_or_error = Pod::unmarshal(objs[idx].clone());
            if pod_or_error.is_ok() {
                pods.push(pod_or_error.unwrap());
                proof {
                    // Show that the pods Vec and the model_result are equal up to index idx + 1.
                    let model_result = model_reconciler::objects_to_pods(objs.deep_view());
                    if (model_result.is_some()) {
                        assert(model_result.unwrap().take((idx + 1) as int)
                            == model_result.unwrap().take(idx as int) + seq![model_result.unwrap()[idx as int]]);
                        assert_seqs_equal!(
                            pods.deep_view(),
                            model_result.unwrap().take((idx + 1) as int)
                        );
                    }
                }
            } else {
                proof {
                    // Show that if a pod was unable to be serialized, the model would return None.
                    let model_input = objs.deep_view();
                    let model_result = model_reconciler::objects_to_pods(model_input);
                    assert(
                        model_input
                            .filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err())
                            .contains(model_input[idx as int])
                    );
                    assert(model_result == None::<Seq<PodView>>);
                }
                return None;
            }
        }

        proof {
            let model_input = objs.deep_view();
            let model_result = model_reconciler::objects_to_pods(model_input);

            // Prove, by contradiction, that the model_result can't be None.
            let filter_result = model_input.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err());
            assert(filter_result.len() == 0) by {
                if filter_result.len() != 0 {
                    seq_filter_contains_implies_seq_contains(
                        model_input,
                        |o: DynamicObjectView| PodView::unmarshal(o).is_err(),
                        filter_result[0]
                    );
                }
            };
            assert(model_result.is_some());

            assert(model_result.unwrap().take(objs.len() as int) == model_result.unwrap());
        }

        Some(pods)
    }

    pub fn make_owner_references(vsts: VStatefulSet) -> (references: Vec<OwnerReference>)
        requires vsts@.well_formed()
        ensures references.deep_view() =~= model_reconciler::make_owner_references(vsts@)
    {
        vec![vsts.controller_owner_ref()]
    }

    pub fn filter_pods(pods: Vec<Pod>, vsts: &VStatefulSet) -> (filtered: Vec<Pod>)
        requires vsts@.well_formed()
        ensures filtered.deep_view() =~= model_reconciler::filter_pods(pods.deep_view(), vsts@)
    {

        assert(vsts@.well_formed());
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
                assert(vsts@.well_formed());
                assert(vsts@.metadata.well_formed_for_namespaced());

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
