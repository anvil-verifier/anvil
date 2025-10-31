use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::trusted::exec_types::VStatefulSet;
use crate::{
    vstatefulset_controller::model::reconciler as model_reconciler,
    vstatefulset_controller::trusted::reconciler as trusted_reconciler,
    vstd_ext::string_view::i32_to_string,
};
use vstd::prelude::*;

verus! {

    // pub open spec fn filter_pods(pods: Vec<Pod>, vsts: VStatefulSet) -> Vec<Pod> {
    //     pods.filter(|pod: Pod|
    //     // See https://github.com/kubernetes/kubernetes/blob/master/pkg/controller/controller_ref_manager.go#L72-L82
    //         pod.metadata.owner_references_contains(&vsts.controller_owner_ref())
    //         && vsts.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
    //         // See https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/controller/statefulset/stateful_set.go#L311-L314
    //         && trusted_reconciler::get_ordinal(vsts.metadata().name().unwrap_or_default()) is Some
    //     )
    // }        

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
