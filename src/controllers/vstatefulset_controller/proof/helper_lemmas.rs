use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vstatefulset_controller::trusted::{spec_types::*, rely::*};
use crate::vstatefulset_controller::model::reconciler::*;
use crate::vstatefulset_controller::proof::predicate::*;
use crate::vstd_ext::seq_lib::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub proof fn vsts_rely_condition_equivalent_to_lifted_vsts_rely_condition(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    ensures
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vsts_rely(other_id, cluster.installed_types)))))
        <==>
            spec.entails(always(lifted_vsts_rely_condition(cluster, controller_id))),
{}

pub open spec fn get_largest_ordinal_of_unmatched_properties(vsts: VStatefulSetView, pods: Seq<Option<PodView>>) -> bool {
    let ordinal = get_largest_ordinal_of_unmatched_pods(vsts, pods);
    ordinal is Some ==> {
        &&& 0 <= ordinal->0 < pods.len()
        &&& pods[ordinal->0 as int] is Some
    }
}

pub proof fn lemma_get_largest_ordinal_of_unmatched_well_behaved(vsts: VStatefulSetView, pods: Seq<Option<PodView>>)
    ensures get_largest_ordinal_of_unmatched_properties(vsts, pods)
{
    let ordinal = get_largest_ordinal_of_unmatched_pods(vsts, pods);
    if ordinal is Some {
        let ordinals = Seq::new(pods.len(), |i: int| i as nat);
        let pred = |ordinal: nat| pods[ordinal as int] is Some && !pod_matches(vsts, pods[ordinal as int]->0);
        let filtered = ordinals.filter(pred);

        assert(filtered.len() > 0);
        assert(ordinal->0 == filtered.last());

        assert(filtered.contains(ordinal->0));
        seq_filter_contains_implies_seq_contains(ordinals, pred, ordinal->0);
        assert(ordinals.contains(ordinal->0));

        assert(0 <= ordinal->0 < pods.len());

        assert(pred(ordinal->0));
        assert(pods[ordinal->0 as int] is Some);
    }
}

}
