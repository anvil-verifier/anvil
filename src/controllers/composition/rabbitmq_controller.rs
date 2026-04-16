use crate::composition::vstatefulset_controller;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::{
    install::*, reconciler::*, resource::stateful_set::make_stateful_set,
};
use crate::rabbitmq_controller::trusted::{
    liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*,
};
use crate::rabbitmq_controller::proof::{
    guarantee::guarantee_condition_holds, predicate::*, liveness::spec::{next_with_wf, next_with_wf_is_stable}
};
use crate::rabbitmq_controller::proof::composition::composed_rmq_eventually_stable_reconciliation;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vstatefulset_controller::model::{
    install::vsts_controller_model, reconciler::VStatefulSetReconciler,
};
use crate::vstatefulset_controller::trusted::{
    liveness_theorem as vsts_liveness_theorem, rely_guarantee as vsts_rely_mod, spec_types::VStatefulSetView,
};

use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

use crate::vdeployment_controller::model::reconciler::VDeploymentReconciler;
use crate::vdeployment_controller::trusted::rely_guarantee::*;
use crate::vreplicaset_controller::model::reconciler::VReplicaSetReconciler;
use crate::vreplicaset_controller::trusted::rely_guarantee::*;
use crate::vreplicaset_controller::trusted::spec_types::VReplicaSetView;

verus! {



impl Composition for RabbitmqReconciler {
    open spec fn c() -> ControllerSpec {
        ControllerSpec{
            esr: rmq_composed_eventually_stable_reconciliation(),
            liveness_dependency: vsts_liveness_theorem::vsts_eventually_stable_reconciliation(),
            safety_guarantee: always(lift_state(rmq_guarantee(Self::id()))),
            safety_partial_rely: |other_id: int| always(lift_state(rmq_rely(other_id))),
            fairness: |cluster: Cluster| next_with_wf(cluster, Self::id()),
            membership: |cluster: Cluster, id: int| {
                &&& cluster.controller_models.contains_pair(VStatefulSetReconciler::id(), vsts_controller_model())
                &&& cluster.controller_models.contains_pair(Self::id(), rabbitmq_controller_model())
                &&& cluster.type_is_installed_in_cluster::<RabbitmqClusterView>()
                &&& cluster.type_is_installed_in_cluster::<VStatefulSetView>()
            },
        }
    }

    open spec fn id() -> int { 4 }

    open spec fn composed() -> Map<int, ControllerSpec> {
        Map::<int, ControllerSpec>::empty()
            .insert(VStatefulSetReconciler::id(), VStatefulSetReconciler::c())
            .insert(VReplicaSetReconciler::id(), VReplicaSetReconciler::c())
            .insert(VDeploymentReconciler::id(), VDeploymentReconciler::c())
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
        let rmq_guarantee = rmq_guarantee(Self::id());

        {
            let vsts_guarantee = vsts_rely_mod::vsts_guarantee(VStatefulSetReconciler::id());
            let rmq_rely_vsts = rmq_rely(VStatefulSetReconciler::id());
            let vsts_rely_rmq = vsts_rely_mod::vsts_rely(Self::id());
            assert(Self::composed().contains_key(VStatefulSetReconciler::id())); // trigger

            assert(lift_state(vsts_guarantee).entails(lift_state(rmq_rely_vsts))) by {
                assert forall |s: ClusterState| #[trigger] vsts_guarantee(s) implies rmq_rely_vsts(s) by {
                    assert forall |msg| #[trigger] s.in_flight().contains(msg)
                        && msg.content is APIRequest
                        && msg.src.is_controller_id(VStatefulSetReconciler::id())
                        implies (match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::UpdateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::GetThenUpdateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::DeleteRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::GetThenDeleteRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::UpdateStatusRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::GetThenUpdateStatusRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(req.obj.kind == Kind::PodKind || req.obj.kind == Kind::PersistentVolumeClaimKind);
                                assert(!is_rmq_managed_kind(req.obj.kind));
                            }
                            APIRequest::GetThenUpdateRequest(req) => {
                                assert(req.obj.kind == Kind::PodKind);
                                assert(!is_rmq_managed_kind(req.obj.kind));
                            }
                            APIRequest::GetThenDeleteRequest(req) => {
                                assert(req.key.kind == Kind::PodKind);
                                assert(!is_rmq_managed_kind(req.key.kind));
                            }
                            _ => {}
                        }
                    };
                };
            }
            assert(spec.entails(always(lift_state(vsts_guarantee)))) by {
                assert(Self::composed()[VStatefulSetReconciler::id()] == VStatefulSetReconciler::c());
            }
            always_weaken(spec, lift_state(vsts_guarantee), lift_state(rmq_rely_vsts));

            assert(lift_state(rmq_guarantee).entails(lift_state(vsts_rely_rmq))) by {
                assert forall |s: ClusterState| #[trigger] rmq_guarantee(s) implies vsts_rely_rmq(s) by {
                    assert forall |msg| #[trigger] s.in_flight().contains(msg)
                        && msg.content is APIRequest
                        && msg.src.is_controller_id(Self::id())
                        implies (match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => vsts_rely_mod::rely_create_req(req),
                            APIRequest::UpdateRequest(req) => vsts_rely_mod::rely_update_req(req)(s),
                            APIRequest::GetThenUpdateRequest(req) => vsts_rely_mod::rely_get_then_update_req(req),
                            APIRequest::DeleteRequest(req) => vsts_rely_mod::rely_delete_req(req)(s),
                            APIRequest::GetThenDeleteRequest(req) => vsts_rely_mod::rely_get_then_delete_req(req),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(rmq_guarantee_create_req(req));
                                assert(is_rmq_managed_kind(req.obj.kind));
                                assert(req.obj.kind != Kind::PodKind);
                                assert(req.obj.kind != Kind::PersistentVolumeClaimKind);
                            }
                            APIRequest::UpdateRequest(req) => {
                                assert(rmq_guarantee_update_req(req));
                                assert(is_rmq_managed_kind(req.obj.kind));
                                assert(req.obj.kind != Kind::PodKind);
                                assert(req.obj.kind != Kind::PersistentVolumeClaimKind);
                            }
                            _ => {}
                        }
                    };
                };
            }
            always_weaken(spec, lift_state(rmq_guarantee), lift_state(vsts_rely_rmq));
        }

        {
            let vrs_guar = vrs_guarantee(VReplicaSetReconciler::id());
            let rmq_rely_vrs = rmq_rely(VReplicaSetReconciler::id());
            let vrs_rely_rmq = vrs_rely(Self::id());
            assert(Self::composed().contains_key(VReplicaSetReconciler::id())); // trigger

            assert(lift_state(vrs_guar).entails(lift_state(rmq_rely_vrs))) by {
                assert forall |s: ClusterState| #[trigger] vrs_guar(s) implies rmq_rely_vrs(s) by {
                    assert forall |msg| #[trigger] s.in_flight().contains(msg)
                        && msg.content is APIRequest
                        && msg.src.is_controller_id(VReplicaSetReconciler::id())
                        implies (match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::UpdateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::GetThenUpdateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::DeleteRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::GetThenDeleteRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::UpdateStatusRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::GetThenUpdateStatusRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(vrs_guarantee_create_req(req)(s));
                                assert(req.obj.kind == Kind::PodKind);
                                assert(!is_rmq_managed_kind(req.obj.kind));
                            }
                            APIRequest::GetThenDeleteRequest(req) => {
                                assert(vrs_guarantee_get_then_delete_req(req)(s));
                                assert(req.key.kind == Kind::PodKind);
                                assert(!is_rmq_managed_kind(req.key.kind));
                            }
                            APIRequest::GetThenUpdateStatusRequest(req) => {
                                assert(vrs_guarantee_get_then_update_status_req(req));
                                assert(req.obj.kind == VReplicaSetView::kind());
                                reveal_strlit("vreplicaset");
                                reveal_strlit("vstatefulset");
                                assert("vreplicaset"@.len() != "vstatefulset"@.len());
                                assert(!is_rmq_managed_kind(req.obj.kind));
                            }
                            APIRequest::ListRequest(_) => {}
                            _ => {
                                // VRS guarantee says false for all other request types
                                assert(false);
                            }
                        }
                    };
                };
            }
            assert(spec.entails(always(lift_state(vrs_guar)))) by {
                assert(Self::composed()[VReplicaSetReconciler::id()] == VReplicaSetReconciler::c());
            }
            always_weaken(spec, lift_state(vrs_guar), lift_state(rmq_rely_vrs));

            assert(lift_state(rmq_guarantee).entails(lift_state(vrs_rely_rmq))) by {
                assert forall |s: ClusterState| #[trigger] rmq_guarantee(s) implies vrs_rely_rmq(s) by {
                    assert forall |msg| #[trigger] s.in_flight().contains(msg)
                        && msg.content is APIRequest
                        && msg.src.is_controller_id(Self::id())
                        implies (match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => vrs_rely_create_req(req)(s),
                            APIRequest::UpdateRequest(req) => vrs_rely_update_req(req)(s),
                            APIRequest::GetThenUpdateRequest(req) => vrs_rely_get_then_update_req(req)(s),
                            APIRequest::UpdateStatusRequest(req) => vrs_rely_update_status_req(req)(s),
                            APIRequest::DeleteRequest(req) => vrs_rely_delete_req(req)(s),
                            APIRequest::GetThenDeleteRequest(req) => vrs_rely_get_then_delete_req(req)(s),
                            APIRequest::GetThenUpdateStatusRequest(req) => vrs_rely_get_then_update_status_req(req)(s),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(rmq_guarantee_create_req(req));
                                assert(is_rmq_managed_kind(req.obj.kind));
                                assert(req.obj.kind != Kind::PodKind);
                            }
                            APIRequest::UpdateRequest(req) => {
                                assert(rmq_guarantee_update_req(req));
                                assert(is_rmq_managed_kind(req.obj.kind));
                                assert(req.obj.kind != Kind::PodKind);
                            }
                            _ => {}
                        }
                    };
                };
            }
            always_weaken(spec, lift_state(rmq_guarantee), lift_state(vrs_rely_rmq));
        }

        {
            let vd_guarantee = vd_guarantee(VDeploymentReconciler::id());
            let rmq_rely_vd = rmq_rely(VDeploymentReconciler::id());
            let vd_rely_rmq = vd_rely(Self::id());
            assert(Self::composed().contains_key(VDeploymentReconciler::id())); // trigger

            assert(lift_state(vd_guarantee).entails(lift_state(rmq_rely_vd))) by {
                assert forall |s: ClusterState| #[trigger] vd_guarantee(s) implies rmq_rely_vd(s) by {
                    assert forall |msg| #[trigger] s.in_flight().contains(msg)
                        && msg.content is APIRequest
                        && msg.src.is_controller_id(VDeploymentReconciler::id())
                        implies (match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::UpdateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::GetThenUpdateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::DeleteRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::GetThenDeleteRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::UpdateStatusRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            APIRequest::GetThenUpdateStatusRequest(req) => !is_rmq_managed_kind(req.key().kind),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(vd_guarantee_create_req(req)(s));
                                assert(req.obj.kind == VReplicaSetView::kind());
                                // Prove VReplicaSetView::kind() != VStatefulSetView::kind()
                                reveal_strlit("vreplicaset");
                                reveal_strlit("vstatefulset");
                                assert("vreplicaset"@.len() != "vstatefulset"@.len());
                                assert(!is_rmq_managed_kind(req.obj.kind));
                            }
                            APIRequest::GetThenUpdateRequest(req) => {
                                assert(vd_guarantee_get_then_update_req(req)(s));
                                assert(req.obj.kind == VReplicaSetView::kind());
                                reveal_strlit("vreplicaset");
                                reveal_strlit("vstatefulset");
                                assert("vreplicaset"@.len() != "vstatefulset"@.len());
                                assert(!is_rmq_managed_kind(req.obj.kind));
                            }
                            APIRequest::GetThenDeleteRequest(req) => {
                                assert(vd_guarantee_get_then_delete_req(req)(s));
                                assert(false); // VD never deletes
                            }
                            _ => {}
                        }
                    };
                };
            }
            assert(spec.entails(always(lift_state(vd_guarantee)))) by {
                assert(Self::composed()[VDeploymentReconciler::id()] == VDeploymentReconciler::c());
            }
            always_weaken(spec, lift_state(vd_guarantee), lift_state(rmq_rely_vd));

            assert(lift_state(rmq_guarantee).entails(lift_state(vd_rely_rmq))) by {
                assert forall |s: ClusterState| #[trigger] rmq_guarantee(s) implies vd_rely_rmq(s) by {
                    assert forall |msg| #[trigger] s.in_flight().contains(msg)
                        && msg.content is APIRequest
                        && msg.src.is_controller_id(Self::id())
                        implies (match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => vd_rely_create_req(req)(s),
                            APIRequest::UpdateRequest(req) => vd_rely_update_req(req)(s),
                            APIRequest::GetThenUpdateRequest(req) => vd_rely_get_then_update_req(req)(s),
                            APIRequest::UpdateStatusRequest(req) => vd_rely_update_status_req(req)(s),
                            APIRequest::DeleteRequest(req) => vd_rely_delete_req(req)(s),
                            APIRequest::GetThenDeleteRequest(req) => vd_rely_get_then_delete_req(req)(s),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(rmq_guarantee_create_req(req));
                                assert(is_rmq_managed_kind(req.obj.kind));
                                reveal_strlit("vreplicaset");
                                reveal_strlit("vstatefulset");
                                assert("vreplicaset"@.len() != "vstatefulset"@.len());
                                assert(req.obj.kind != VReplicaSetView::kind());
                            }
                            APIRequest::UpdateRequest(req) => {
                                assert(rmq_guarantee_update_req(req));
                                assert(is_rmq_managed_kind(req.obj.kind));
                                reveal_strlit("vreplicaset");
                                reveal_strlit("vstatefulset");
                                assert("vreplicaset"@.len() != "vstatefulset"@.len());
                                assert(req.obj.kind != VReplicaSetView::kind());
                            }
                            _ => {}
                        }
                    };
                };
            }
            always_weaken(spec, lift_state(rmq_guarantee), lift_state(vd_rely_rmq));
        }
    }
}

impl VerticalComposition for RabbitmqReconciler {
    proof fn esr_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().esr),
    {
        composed_rmq_eventually_stable_reconciliation(
            spec, cluster, Self::id()
        );
    }

    proof fn liveness_dependency_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_dependency),
    {
        assert(Self::composed().contains_key(VStatefulSetReconciler::id())); // trigger
    }
}

}
