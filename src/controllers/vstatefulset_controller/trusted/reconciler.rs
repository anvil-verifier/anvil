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

    #[verifier(external_body)]
    pub fn get_ordinal(parent_name: &String, pod: &Pod) -> (ordinal: Option<usize>)
        ensures (
            (ordinal@ matches Some(v1) && model_reconciler::get_ordinal(parent_name@, pod@) matches Some(v2) && v1 == v2)
            || (ordinal@ matches None && model_reconciler::get_ordinal(parent_name@, pod@) matches None)
        )
    {
        pod.metadata()
            .name()
            .and_then(|name| name[parent_name.len() + 1..].parse::<usize>().ok())
    }

    #[verifier(external_body)]
    pub fn sort_pods_by_ord(parent_name: &String, pods: &mut Vec<Pod>) 
        ensures pods.deep_view() == old(pods).deep_view().sort_by(|p1: PodView, p2: PodView| model_reconciler::get_ordinal(parent_name@, p1)->0 >= model_reconciler::get_ordinal(parent_name@, p2)->0)
    {
        pods.sort_by(|p1, p2| get_ordinal(parent_name, p2).cmp(&get_ordinal(parent_name, p1)));
    }
}
