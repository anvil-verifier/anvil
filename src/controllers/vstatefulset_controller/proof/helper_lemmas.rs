use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vstatefulset_controller::trusted::spec_types::*;
use crate::vstatefulset_controller::model::reconciler::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub proof fn lemma_get_largest_ordinal_of_unmatched_properties_well_behaved(vsts: VStatefulSetView, pods: Seq<Option<PodView>>)
    ensures
        ({
            let ordinal = get_largest_ordinal_of_unmatched_pods(vsts, pods);
            ordinal is Some ==> {
                &&& 0 <= ordinal->0 < pods.len()
                &&& pods[ordinal->0 as int] is Some
            }
        })
{

}

}
