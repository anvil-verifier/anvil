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
    pub fn get_ordinal(parent_name: String, pod: Pod) -> (ordinal: Option<i32>)
        ensures (
            (ordinal@ matches Some(v1) && model_reconciler::get_ordinal(parent_name@, pod@) matches Some(v2) && v1 == v2)
            || (ordinal@ matches None && model_reconciler::get_ordinal(parent_name@, pod@) matches None)
        )
    {
        pod.metadata()
            .name()
            .and_then(|name| name[parent_name.len() + 1..].parse::<i32>().ok())
    }
}
