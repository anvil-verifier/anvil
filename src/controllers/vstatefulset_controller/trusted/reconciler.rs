use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::{
    vstatefulset_controller::model::reconciler as model_reconciler,
    vstd_ext::string_view::i32_to_string,
};
use vstd::prelude::*;

verus! {

    // TODO: verify these functions
    #[verifier(external_body)]
    pub fn get_ordinal(parent_name: &String, pod_name: &String) -> (ordinal: Option<usize>)
        ensures (
            (ordinal@ matches Some(v1) && model_reconciler::get_ordinal(parent_name@, pod_name@) matches Some(v2) && v1 == v2)
            || (ordinal@ matches None && model_reconciler::get_ordinal(parent_name@, pod_name@) matches None)
        )
    {
        pod_name["vstatefulset".len() + parent_name.len() + 2..].parse::<usize>().ok()
    }

    #[verifier(external_body)]
    pub fn sort_pods_by_ord(parent_name: &String, pods: &mut Vec<Pod>) 
        ensures pods.deep_view() == old(pods).deep_view().sort_by(|p1: PodView, p2: PodView| model_reconciler::get_ordinal(parent_name@, p1.metadata.name->0)->0 >= model_reconciler::get_ordinal(parent_name@, p2.metadata.name->0)->0)
    {
        pods.sort_by(|p1: &Pod, p2: &Pod| get_ordinal(parent_name, &p2.metadata().name().unwrap()).cmp(&get_ordinal(parent_name, &p1.metadata().name().unwrap())));
    }
}
