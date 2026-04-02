use crate::kubernetes_cluster::proof::composition::*;
use crate::vdeployment_controller::model::reconciler::VDeploymentReconciler;
use crate::vdeployment_controller::trusted::rely_guarantee::*;
use crate::vreplicaset_controller::{
    model::reconciler::{VReplicaSetReconciler, has_vrs_prefix},
    trusted::spec_types::*,
};
use crate::vreplicaset_controller::trusted::rely_guarantee::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::proof::predicate::*;
use crate::vstatefulset_controller::trusted::{
    spec_types::*, rely_guarantee::*, liveness_theorem::*
};
use crate::vstatefulset_controller::model::{
    reconciler::*, install::*
};
use crate::vstatefulset_controller::proof::{
    guarantee::*, liveness::spec::*
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{

// Helper lemma: vsts and vrs prefixes are disjoint
proof fn vsts_prefix_not_vrs_prefix(name: StringView)
    ensures
        !(has_vsts_prefix(name) && has_vrs_prefix(name)),
{
    if has_vsts_prefix(name) && has_vrs_prefix(name) {
        let vsts_suffix = choose |suffix| name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + suffix;
        let vrs_suffix = choose |suffix| name == VReplicaSetView::kind()->CustomResourceKind_0 + "-"@ + suffix;
        assert(VStatefulSetView::kind()->CustomResourceKind_0 == "vstatefulset"@);
        assert(VReplicaSetView::kind()->CustomResourceKind_0 == "vreplicaset"@);
        assert(name.take(VStatefulSetView::kind()->CustomResourceKind_0.len() as int) == VStatefulSetView::kind()->CustomResourceKind_0);
        assert(name.take(VReplicaSetView::kind()->CustomResourceKind_0.len() as int) == VReplicaSetView::kind()->CustomResourceKind_0);
        vrs_vsts_str_neq();
        assert(VStatefulSetView::kind()->CustomResourceKind_0.len() > VReplicaSetView::kind()->CustomResourceKind_0.len());
        assert(VStatefulSetView::kind()->CustomResourceKind_0.take(VReplicaSetView::kind()->CustomResourceKind_0.len() as int) == VReplicaSetView::kind()->CustomResourceKind_0);
        assert(false);
    }
}

// Helper lemma: VRS and VD controllers have distinct IDs
#[verifier(external_body)]
proof fn vrs_id_ne_vd_id()
    ensures VReplicaSetReconciler::id() != VDeploymentReconciler::id(),
{}

impl Composition for VStatefulSetReconciler {
    open spec fn c() -> ControllerSpec {
        ControllerSpec{
            liveness_guarantee: vsts_eventually_stable_reconciliation(),
            liveness_rely: true_pred(), // VSTS does not require assumptions of other controller's ESR
            safety_guarantee: always(lift_state(vsts_guarantee(Self::id()))),
            safety_partial_rely: |other_id: int| always(lift_state(vsts_rely(other_id))),
            fairness: |cluster: Cluster| next_with_wf(cluster, Self::id()),
            membership: |cluster: Cluster, id: int| {
                &&& cluster.controller_models.contains_pair(id, vsts_controller_model())
                &&& cluster.type_is_installed_in_cluster::<VStatefulSetView>()
            },
        }
    }

    uninterp spec fn id() -> int;

    open spec fn composed() -> Map<int, ControllerSpec> {
        Map::empty().insert(VReplicaSetReconciler::id(), VReplicaSetReconciler::c()).insert(VDeploymentReconciler::id(), VDeploymentReconciler::c())
    }

    proof fn safety_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
    ensures
        spec.entails(Self::c().safety_guarantee),
    {
        guarantee_condition_holds(spec, cluster, Self::id());
    }

    proof fn safety_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
    ensures
        forall |i| #[trigger] Self::composed().contains_key(i) ==>
            spec.entails((Self::c().safety_partial_rely)(i))
            && spec.entails((Self::composed()[i].safety_partial_rely)(Self::id()))
    {
        let vsts_guar = vsts_guarantee(Self::id());
        let vsts_rely_vrs = vsts_rely(VReplicaSetReconciler::id());
        let vrs_guar = vrs_guarantee(VReplicaSetReconciler::id());
        let vrs_rely_vsts = vrs_rely(Self::id());
        assert(Self::composed().contains_key(VReplicaSetReconciler::id())); // trigger
        assert(lift_state(vrs_guar).entails(lift_state(vsts_rely_vrs))) by {
            assert forall |s: ClusterState| #[trigger] vrs_guar(s) implies vsts_rely_vrs(s) by {
                assert forall |msg| #[trigger] s.in_flight().contains(msg) && msg.content is APIRequest && msg.src.is_controller_id(VReplicaSetReconciler::id()) implies (
                    match msg.content->APIRequest_0 {
                        APIRequest::CreateRequest(req) => rely_create_req(req),
                        APIRequest::UpdateRequest(req) => rely_update_req(req)(s),
                        APIRequest::GetThenUpdateRequest(req) => rely_get_then_update_req(req),
                        APIRequest::DeleteRequest(req) => rely_delete_req(req)(s),
                        APIRequest::GetThenDeleteRequest(req) => rely_get_then_delete_req(req),
                        _ => true,
                    }
                ) by {
                    let req = msg.content->APIRequest_0;
                    match req {
                        APIRequest::CreateRequest(r) => {
                            assert(vrs_guarantee_create_req(r)(s));
                            vsts_prefix_not_vrs_prefix(r.obj.metadata.generate_name->0);
                        }
                        APIRequest::GetThenDeleteRequest(r) => {
                            assert(vrs_guarantee_get_then_delete_req(r)(s));
                            vsts_prefix_not_vrs_prefix(r.key.name);
                        }
                        _ => {}
                    }
                };
            };
        }
        assert(spec.entails(always(lift_state(vrs_guar)))) by {
            vrs_id_ne_vd_id();
            assert(Self::composed()[VReplicaSetReconciler::id()] == VReplicaSetReconciler::c());
        }
        always_weaken(spec, lift_state(vrs_guar), lift_state(vsts_rely_vrs));

        // vsts_guarantee alone implies vrs_rely
        assert(lift_state(vsts_guar).entails(lift_state(vrs_rely_vsts))) by {
            assert forall |s: ClusterState| #[trigger] vsts_guar(s) implies vrs_rely_vsts(s) by {
                assert forall |msg| #[trigger] s.in_flight().contains(msg) && msg.content is APIRequest && msg.src.is_controller_id(Self::id()) implies (
                    match msg.content->APIRequest_0 {
                        APIRequest::CreateRequest(req) => vrs_rely_create_req(req)(s),
                        APIRequest::UpdateRequest(req) => vrs_rely_update_req(req)(s),
                        APIRequest::GetThenUpdateRequest(req) => vrs_rely_get_then_update_req(req)(s),
                        APIRequest::UpdateStatusRequest(req) => vrs_rely_update_status_req(req)(s),
                        APIRequest::DeleteRequest(req) => vrs_rely_delete_req(req)(s),
                        APIRequest::GetThenDeleteRequest(req) => vrs_rely_get_then_delete_req(req)(s),
                        APIRequest::GetThenUpdateStatusRequest(req) => vrs_rely_get_then_update_status_req(req)(s),
                        _ => true,
                    }
                ) by {
                    let req = msg.content->APIRequest_0;
                    match req {
                        APIRequest::CreateRequest(r) => {
                            assert(vsts_guarantee_create_req(r));
                            vsts_prefix_not_vrs_prefix(r.obj.metadata.name->0);
                        }
                        APIRequest::GetThenUpdateRequest(r) => {
                            assert(vsts_guarantee_get_then_update_req(r));
                            vsts_prefix_not_vrs_prefix(r.name);
                        }
                        APIRequest::GetThenDeleteRequest(r) => {
                            assert(vsts_guarantee_get_then_delete_req(r));
                            vsts_prefix_not_vrs_prefix(r.key.name);
                        }
                        _ => {}
                    }
                };
            };
        }
        always_weaken(spec, lift_state(vsts_guar), lift_state(vrs_rely_vsts));

        // For i = VDeploymentReconciler::id()
        let vsts_rely_vd = vsts_rely(VDeploymentReconciler::id());
        let vd_guar = vd_guarantee(VDeploymentReconciler::id());
        let vd_rely_vsts = vd_rely(Self::id());
        assert(Self::composed().contains_key(VDeploymentReconciler::id())); // trigger
        assert(lift_state(vsts_guar).and(lift_state(vd_guar)).entails(lift_state(vsts_rely_vd).and(lift_state(vd_rely_vsts))));
        assert(spec.entails(always(lift_state(vd_guar)))) by {
            vrs_id_ne_vd_id();
            assert(Self::composed()[VDeploymentReconciler::id()] == VDeploymentReconciler::c());
        }
        entails_and_temp(spec, always(lift_state(vsts_guar)), always(lift_state(vd_guar)));
        always_and_equality(lift_state(vsts_guar), lift_state(vd_guar));
        always_weaken(spec, lift_state(vsts_guar).and(lift_state(vd_guar)), lift_state(vsts_rely_vd).and(lift_state(vd_rely_vsts)));
        always_and_equality(lift_state(vsts_rely_vd), lift_state(vd_rely_vsts));
        entails_trans(spec,
            always(lift_state(vsts_rely_vd)).and(always(lift_state(vd_rely_vsts))),
            always(lift_state(vsts_rely_vd))
        );
        entails_trans(spec,
            always(lift_state(vsts_rely_vd)).and(always(lift_state(vd_rely_vsts))),
            always(lift_state(vd_rely_vsts))
        );
    }
}

impl HorizontalComposition for VStatefulSetReconciler {
    proof fn liveness_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_guarantee),
    {
        assume(false);
    }
}

}