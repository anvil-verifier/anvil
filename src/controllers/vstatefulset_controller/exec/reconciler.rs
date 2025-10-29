use crate::{
    vstatefulset_controller::model::reconciler as model_reconciler,
    vstd_ext::string_view::i32_to_string,
};
use vstd::prelude::*;

verus! {

    pub fn pod_name(parent_name: String, ordinal: i32) -> (result: String)
        requires ordinal >= 0
        ensures result@ == model_reconciler::pod_name(parent_name@, ordinal as nat)
    {
        parent_name
        .concat("-")
        .concat(i32_to_string(ordinal).as_str())
    }

}
