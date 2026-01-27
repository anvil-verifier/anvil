use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*,
    api_server::types::*,
    network::state_machine::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_invariants, predicate::*, guarantee::*},
    trusted::{rely::*, spec_types::*,  liveness_theorem::*, step::VStatefulSetReconcileStepView::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*, string_view::*};
use vstd::{seq_lib::*, map_lib::*, set_lib::*};
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
            spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
{}


pub proof fn get_ordinal_eq_pod_name(vsts_name: StringView, ord: nat, compared_pod_name: StringView)
ensures
    (get_ordinal(vsts_name, compared_pod_name) == Some(ord))
        <==> compared_pod_name == pod_name(vsts_name, ord)
{
    if pod_name(vsts_name, ord) == compared_pod_name {
        assert(get_ordinal(vsts_name, compared_pod_name) is Some);
        if get_ordinal(vsts_name, compared_pod_name) != Some(ord) {
            let havoc_ord = get_ordinal(vsts_name, compared_pod_name)->0;
            assert(pod_name(vsts_name, havoc_ord) == pod_name(vsts_name, ord));
            assert(pod_name(vsts_name, havoc_ord) ==
                VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + vsts_name + "-"@ + int_to_string_view(havoc_ord as int));
            assert(pod_name(vsts_name, ord) ==
                VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + vsts_name + "-"@ + int_to_string_view(ord as int));
            assert(VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + vsts_name + "-"@ + int_to_string_view(havoc_ord as int)
                == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + vsts_name + "-"@ + int_to_string_view(ord as int));
            if int_to_string_view(havoc_ord as int) != int_to_string_view(ord as int) {
                seq_unequal_preserved_by_add_prefix(
                    VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + vsts_name + "-"@,
                    int_to_string_view(havoc_ord as int),
                    int_to_string_view(ord as int)
                );
                assert(false);
            }
            int_to_string_view_injectivity();
            assert(false);
        }
    }
}

#[verifier(external_body)]
pub proof fn pvc_name_with_vsts_match_vsts(
    name: StringView, vsts: VStatefulSetView
)
requires
    // index, ord
    exists |i: (nat, nat)| name == #[trigger]
        pvc_name(vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0, vsts.metadata.name->0, i.1),
ensures
    pvc_name_match(name, vsts.metadata.name->0),
{}
}
