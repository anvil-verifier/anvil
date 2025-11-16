use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::trusted::exec_types::VStatefulSet;
use crate::vstatefulset_controller::trusted::reconciler::get_ordinal;
use crate::vstatefulset_controller::trusted::reconciler::sort_pods_by_ord;
use crate::vstd_ext::string_view::StringView;
use crate::vstd_ext::{seq_lib::*, string_map::StringMap};
use crate::{
    vstatefulset_controller::model::reconciler as model_reconciler,
    vstatefulset_controller::trusted::reconciler as trusted_reconciler,
    vstd_ext::string_view::u32_to_string,
};
use std::collections::BTreeSet;
use vstd::relations::{sorted_by, total_ordering};
use vstd::{prelude::*, seq_lib::*};

verus! {

    // pub fn make_pod(vsts: VStatefulSet, ord: i32) -> (pod: Pod)
    //     requires ord >= 0
    //     ensures pod@ == model_reconciler::make_pod(vsts@, ord as nat)
    // {
        
    // }

    pub fn get_pod_with_ord(parent_name: String, pods: &Vec<Pod>, ord: u32) -> (result: Option<Pod>) 
        ensures result.deep_view() == model_reconciler::get_pod_with_ord(parent_name@, pods.deep_view(), ord as nat)
    {
        let mut filtered: Vec<Pod> = Vec::new();
        proof {
            let model_filtered = model_reconciler::filter_pods_by_ord(parent_name@, pods.deep_view().take(0), ord as nat);
            assert(filtered.deep_view() == model_filtered);
        }

        for idx in 0..pods.len()
            invariant idx <= pods.len(),
            filtered.deep_view() == model_reconciler::filter_pods_by_ord(parent_name@, pods.deep_view().take(idx as int), ord as nat)
        {
            let pod = &pods[idx];
            if get_ordinal(&parent_name, pod).is_some() && get_ordinal(&parent_name, pod).unwrap() == ord {
                filtered.push(pod.clone());
            }

            proof {
                let old_filtered = if model_reconciler::pod_has_ord(parent_name@, ord as nat)(pod@) {
                    filtered.deep_view().drop_last()
                } else {
                    filtered.deep_view()
                };
                assert(old_filtered == model_reconciler::filter_pods_by_ord(parent_name@, pods.deep_view().take(idx as int), ord as nat));
                lemma_filter_push(pods.deep_view().take(idx as int), model_reconciler::pod_has_ord(parent_name@, ord as nat), pod@);
                assert(pods.deep_view().take(idx as int).push(pod@) == pods.deep_view().take(idx + 1));
                assert(filtered.deep_view() == model_reconciler::filter_pods_by_ord(parent_name@, pods.deep_view().take(idx + 1 as int), ord as nat));
            }
        }
      
        proof {
            assert(pods.deep_view().take(pods.len() as int) == pods.deep_view());
        }

        assert(filtered.deep_view() == model_reconciler::filter_pods_by_ord(parent_name@, pods.deep_view(), ord as nat));

        if filtered.len() > 0 {
            Some(filtered[0].clone())
        } else {
            None
        }
    }


    pub fn partition_pods(parent_name: String, replicas: u32, pods: Vec<Pod>) -> (result: (Vec<Option<Pod>>, Vec<Pod>))
        requires replicas <= i32::MAX
        ensures result.0.deep_view() == model_reconciler::partition_pods(parent_name@, replicas as nat, pods.deep_view()).0,
                result.1.deep_view() == model_reconciler::partition_pods(parent_name@, replicas as nat, pods.deep_view()).1
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
            invariant 
            replicas <= i32::MAX,
            i <= replicas,
            needed.deep_view() == model_reconciler::partition_pods(parent_name@, replicas as nat, pods.deep_view()).0.take(i as int)
            
            decreases replicas - i
        {
            let pod_or_none = get_pod_with_ord(parent_name.clone(), &pods, i);
            needed.push(pod_or_none);

            proof {
                assert((i as i32) as int == i as int); // this is needed due to some ugly type conversions
                
                let needed_model: Seq<Option<PodView>> = Seq::new(replicas as nat, |ord: int| model_reconciler::get_pod_with_ord(parent_name@, pods.deep_view(), ord as nat));
                let needed_old = needed.deep_view().drop_last();
                let pod = pod_or_none.deep_view();

                assert(needed.deep_view() == needed_old.push(pod));

                assert(needed_old == needed_model.take(i as int));
                assert(needed_model[i as int] == model_reconciler::get_pod_with_ord(parent_name@, pods.deep_view(), i as nat));
                assert(pod_or_none.deep_view() == model_reconciler::get_pod_with_ord(parent_name@, pods.deep_view(), i as nat));
                assert(needed_model[i as int] == pod_or_none.deep_view());
            }

            i += 1;
        }

        let mut condemned: Vec<Pod> = Vec::new();

        proof {
            assert_seqs_equal!(
                condemned.deep_view(),
                pods.deep_view().take(0).filter(|pod: PodView| model_reconciler::get_ordinal(parent_name@, pod) is Some && model_reconciler::get_ordinal(parent_name@, pod)->0 >= replicas)
            );
        }        

        for i in 0..pods.len() 
        invariant 
            replicas <= i32::MAX,
            condemned.deep_view() == pods.deep_view().take(i as int).filter(|pod: PodView| model_reconciler::get_ordinal(parent_name@, pod) is Some && model_reconciler::get_ordinal(parent_name@, pod)->0 >= replicas)
        {
            let pod = &pods[i];
            let ordinal = get_ordinal(&parent_name, pod);
            if ordinal.is_some() && ordinal.unwrap() >= replicas {
                condemned.push(pod.clone());
            } 
        
            proof {
                assert(replicas as i32 == replicas);
                let spec_filter = |pod: PodView| model_reconciler::get_ordinal(parent_name@, pod) is Some && model_reconciler::get_ordinal(parent_name@, pod)->0 >= replicas;
                let old_filtered = if spec_filter(pod@) {
                    condemned.deep_view().drop_last()
                } else {
                    condemned.deep_view()
                };
                assert(old_filtered == pods.deep_view().take(i as int).filter(spec_filter));
                lemma_filter_push(pods.deep_view().take(i as int), spec_filter, pod@);
                assert(pods.deep_view().take(i as int).push(pod@) == pods.deep_view().take(i + 1));
            }
        }

        proof {
            assert(pods.deep_view().take(pods.len() as int) == pods.deep_view());
        }
        
        sort_pods_by_ord(&parent_name, &mut condemned);

        (needed, condemned)

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
                && trusted_reconciler::get_ordinal(&vsts.metadata().name().unwrap(), &pod).is_some() {
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

    pub fn pod_name(parent_name: String, ordinal: u32) -> (result: String)
        ensures result@ == model_reconciler::pod_name(parent_name@, ordinal as nat)
    {
        parent_name
        .concat("-")
        .concat(u32_to_string(ordinal).as_str())
    }

    pub fn pvc_name(pvc_template_name: String, vsts_name: String, ordinal: u32) -> (result: String)
        ensures result@ == model_reconciler::pvc_name(pvc_template_name@, vsts_name@, ordinal as nat)
    {
        pvc_template_name
        .concat("-")
        .concat(pod_name(vsts_name, ordinal).as_str())
    }

}
