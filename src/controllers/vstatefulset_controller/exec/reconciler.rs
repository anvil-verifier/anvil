use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::trusted::exec_types::VStatefulSet;
use crate::vstatefulset_controller::trusted::reconciler::get_ordinal;
use crate::vstd_ext::string_view::StringView;
use crate::vstd_ext::{seq_lib::*, string_map::StringMap};
use crate::{
    vstatefulset_controller::model::reconciler as model_reconciler,
    vstatefulset_controller::trusted::reconciler as trusted_reconciler,
    vstd_ext::string_view::i32_to_string,
};
use std::collections::BTreeSet;
use vstd::relations::{sorted_by, total_ordering};
use vstd::{prelude::*, seq_lib::*};

use core::alloc::Allocator;

verus! {

    // #[verifier(external_body)]
    // fn vec_split_off<T>(vec: &mut Vec<T>, at: usize) -> (return_value: Vec<T>)
    //     // requires
    //     //     at <= old(vec)@.len(),
    //     ensures
    //         vec@ == old(vec)@.subrange(0, at as int),
    //         return_value@ == old(vec)@.subrange(at as int, old(vec)@.len() as int),
    // {
    //     vec.split_off(at)
    // }

    // // Helper function to aid with merge sort

    // spec fn spec_pod_compare(parent_name: StringView, p1: PodView, p2: PodView) -> bool {
    //     model_reconciler::get_ordinal(parent_name, p1)->0 >= model_reconciler::get_ordinal(parent_name, p2)->0
    // }

    // spec fn pods_sorted(parent_name: StringView, pods: Seq<PodView>) -> bool {
    //     sorted_by(pods, |p1: PodView, p2: PodView| spec_pod_compare(parent_name, p1, p2))
    // }

    // fn pod_compare(parent_name: String, p1: &Pod, p2: &Pod) -> (cmp: bool)
    //     ensures cmp == spec_pod_compare(parent_name@, p1@, p2@)
    // {
    //     get_ordinal(parent_name.clone(), p1).unwrap() >= get_ordinal(parent_name, p2).unwrap()
    // }

    // spec fn spec_merge_sorted_pods(parent_name: StringView, left: Seq<PodView>, right: Seq<PodView>) -> Seq<PodView>
    //     recommends
    //         pods_sorted(parent_name, left),
    //         pods_sorted(parent_name, right)
    //     decreases left.len(), right.len(),
    // {
    //     if left.len() == 0 {
    //         right
    //     } else if right.len() == 0 {
    //         left
    //     } else if spec_pod_compare(parent_name, left.first(), right.first()) {
    //         Seq::<PodView>::empty().push(left.first()) + spec_merge_sorted_pods(parent_name, left.drop_first(), right)
    //     } else {
    //         Seq::<PodView>::empty().push(right.first()) + spec_merge_sorted_pods(parent_name, left, right.drop_first())
    //     }

    // }

    // fn merge_sorted_pods(parent_name: String, left: Vec<Pod>, right: Vec<Pod>) -> (result: Vec<Pod>)
    //     requires
    //         sorted_by(left.deep_view(), |p1: PodView, p2: PodView| spec_pod_compare(parent_name@, p1, p2)),
    //         sorted_by(right.deep_view(), |p1: PodView, p2: PodView| spec_pod_compare(parent_name@, p1, p2))
    //     ensures
    //         result.deep_view() == spec_merge_sorted_pods(parent_name@, left.deep_view(), right.deep_view())
    //     decreases left@.len() + right@.len()
    // {
    //     if left.len() == 0 {
    //         right
    //     } else if right.len() == 0 {
    //         left
    //     } else if pod_compare(parent_name.clone(), &left[0], &right[0]) {
    //         let mut result: Vec<Pod> = Vec::new();
    //         let mut left_mut = left.clone();
    //         assert(pods_sorted(parent_name@, left_mut.deep_view()));
    //         let rest = vec_split_off(&mut left_mut, 1);
    //         assume(rest@ =~= left@.subrange(1, left.len() as int));
    //         assert(pods_sorted(parent_name@, rest.deep_view()));
    //         let mut rec = merge_sorted_pods(parent_name, rest, right);
    //         result.push(left[0].clone());
    //         result.append(&mut rec);
    //         result
    //     } else {
    //         right
    //     }
    // }



    // #[verifier(external_erasebody)]
    // fn sort_pods(mut pods: Vec<Pod>, parent_name: String) -> (sorted: Vec<Pod>)
    //     ensures
    //     sorted.deep_view() =~= pods.deep_view()
    //         .sort_by(|p1: PodView, p2: PodView| model_reconciler::get_ordinal(parent_name@, p1)->0 >= model_reconciler::get_ordinal(parent_name@, p2)->0)
    // {
    //     pods.sort_by(|p1, p2| get_ordinal(parent_name.clone(), p2).unwrap().cmp(&get_ordinal(parent_name.clone(), p1).unwrap()));
    //     pods
    // }

    pub fn get_pod_with_ord(parent_name: String, pods: &Vec<Pod>, ord: i32) -> (result: Option<Pod>) 
        ensures result.deep_view() == model_reconciler::get_pod_with_ord(parent_name@, pods.deep_view(), ord as int)
    {
        let mut filtered: Vec<Pod> = Vec::new();
        proof {
            let model_filtered = pods.deep_view().take(0).filter(|pod: PodView| model_reconciler::get_ordinal(parent_name@, pod) is Some && model_reconciler::get_ordinal(parent_name@, pod)->0 == ord);
            assert(filtered.deep_view() == model_filtered);
        }

        for idx in 0..pods.len()
            invariant idx <= pods.len(),
            filtered.deep_view() == pods.deep_view().take(idx as int).filter(|pod: PodView| model_reconciler::get_ordinal(parent_name@, pod) is Some && model_reconciler::get_ordinal(parent_name@, pod)->0 == ord)
        {
            let pod = &pods[idx];
            if get_ordinal(parent_name.clone(), pod).is_some() && get_ordinal(parent_name.clone(), pod).unwrap() == ord {
                filtered.push(pod.clone());
            }

            proof {
                let spec_filter = |pod: PodView| model_reconciler::get_ordinal(parent_name@, pod) is Some && model_reconciler::get_ordinal(parent_name@, pod)->0 == ord;
                let old_filtered = if spec_filter(pod@) {
                    filtered.deep_view().drop_last()
                } else {
                    filtered.deep_view()
                };
                assert(old_filtered == pods.deep_view().take(idx as int).filter(spec_filter));
                lemma_filter_push(pods.deep_view().take(idx as int), spec_filter, pod@);
                assert(pods.deep_view().take(idx as int).push(pod@) == pods.deep_view().take(idx + 1));
            }
        }

        proof {
            let model_filtered = pods.deep_view().filter(|pod: PodView| model_reconciler::get_ordinal(parent_name@, pod) is Some && model_reconciler::get_ordinal(parent_name@, pod)->0 == ord);
            assert(pods.deep_view().take(pods.len() as int) == pods.deep_view());
            assert(filtered.deep_view() == model_filtered);

        }
        let ret = if filtered.len() > 0 {
            Some(filtered[0].clone())
        } else {
            None

        };

        proof {
            reveal(model_reconciler::get_pod_with_ord);
            assume(ret.deep_view() == model_reconciler::get_pod_with_ord(parent_name@, pods.deep_view(), ord as int));
        }
        return ret;
    }


    pub fn partition_pods(parent_name: String, replicas: u32, pods: Vec<Pod>) -> (result: (Vec<Option<Pod>>, Vec<Pod>))
        ensures result.0.deep_view() == model_reconciler::partition_pods(parent_name@, replicas as nat, pods.deep_view()).0,
                // result.1.deep_view() =~= model_reconciler::partition_pods(parent_name@, replicas as nat, pods.deep_view()).1
    {
        // needed includes all the pods that should be created or updated
        // creation/update will start with the beginning of needed where ordinal == 0
        let mut needed: Vec<Option<Pod>> = Vec::new();

        proof {
            assert_seqs_equal!(
                needed.deep_view(),
                model_reconciler::partition_pods(parent_name@, replicas as nat, pods.deep_view()).0.take(0)
            );
        }
        let mut i = 0;
        while i < replicas
            invariant needed.deep_view() == model_reconciler::partition_pods(parent_name@, replicas as nat, pods.deep_view()).0.take(i as int)
            decreases replicas - i
        {
            let pod_or_none = get_pod_with_ord(parent_name.clone(), &pods, i as i32);
            needed.push(pod_or_none);

            proof {
                let needed_model: Seq<Option<PodView>> = Seq::new(replicas as nat, |ord: int| model_reconciler::get_pod_with_ord(parent_name@, pods.deep_view(), ord as int));
                assert(needed.deep_view().drop_last() == needed_model.take(i as int));
                broadcast use group_seq_properties;
                assert(needed_model[i as int] == model_reconciler::get_pod_with_ord(parent_name@, pods.deep_view(), i as int));
                assert(pod_or_none.deep_view() == model_reconciler::get_pod_with_ord(parent_name@, pods.deep_view(), i as int));
            }

            i += 1;
        }

        (needed, vec![])

    }

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
                vsts@.well_formed()
        {
            let pod = &pods[idx];
            if  pod.metadata().owner_references_contains(&vsts.controller_owner_ref())
                && vsts.spec().selector().matches(pod.metadata().labels().unwrap_or(StringMap::empty()))
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
