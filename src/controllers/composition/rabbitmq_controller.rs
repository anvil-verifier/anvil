use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::defs::*;
use crate::rabbitmq_controller::trusted::{
    spec_types::*, rely_guarantee::*, liveness_theorem::*, step::*
};
use crate::rabbitmq_controller::model::{
    reconciler::*, install::*, resource::stateful_set::make_stateful_set
};
use crate::vstatefulset_controller::trusted::{
    spec_types::VStatefulSetView,
    liveness_theorem as vsts_liveness_theorem,
    rely as vsts_rely_mod,
};
use crate::vstatefulset_controller::trusted::rely::vsts_rely;
use crate::vstatefulset_controller::proof::guarantee::{vsts_guarantee, vsts_guarantee_create_req, vsts_guarantee_get_then_update_req, vsts_guarantee_get_then_delete_req};
use crate::vstatefulset_controller::model::{
    reconciler::VStatefulSetReconciler, install::vsts_controller_model
};
use crate::vstatefulset_controller::proof::liveness::spec as vsts_spec;
use crate::composition::vstatefulset_controller;
use crate::temporal_logic::rules::*;

use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

use crate::vdeployment_controller::model::reconciler::VDeploymentReconciler;
use crate::vdeployment_controller::trusted::rely_guarantee::*;
use crate::vreplicaset_controller::model::reconciler::VReplicaSetReconciler;
use crate::vreplicaset_controller::trusted::spec_types::VReplicaSetView;
use crate::vreplicaset_controller::trusted::rely_guarantee::*;

verus !{

#[verifier(external_body)]
proof fn vrs_id_ne_vd_id()
    ensures VReplicaSetReconciler::id() != VDeploymentReconciler::id(),
{}

#[verifier(external_body)]
proof fn vsts_id_ne_vrs_id()
    ensures VStatefulSetReconciler::id() != VReplicaSetReconciler::id(),
{}

#[verifier(external_body)]
proof fn vsts_id_ne_vd_id()
    ensures VStatefulSetReconciler::id() != VDeploymentReconciler::id(),
{}

impl Composition for RabbitmqReconciler {
    open spec fn c() -> ControllerSpec {
        ControllerSpec{
            liveness_guarantee: rmq_composed_eventually_stable_reconciliation(),
            liveness_rely: vsts_liveness_theorem::vsts_eventually_stable_reconciliation(),
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

    uninterp spec fn id() -> int;

    open spec fn composed() -> Map<int, ControllerSpec> {
        Map::<int, ControllerSpec>::empty().insert(VStatefulSetReconciler::id(), VStatefulSetReconciler::c()).insert(VReplicaSetReconciler::id(), VReplicaSetReconciler::c()).insert(VDeploymentReconciler::id(), VDeploymentReconciler::c())
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
            let vsts_guarantee = vsts_guarantee(VStatefulSetReconciler::id());
            let rmq_rely_vsts = rmq_rely(VStatefulSetReconciler::id());
            let vsts_rely_rmq = vsts_rely(Self::id());
            assert(Self::composed().contains_key(VStatefulSetReconciler::id())); // trigger

            assert(lift_state(vsts_guarantee).entails(lift_state(rmq_rely_vsts))) by {
                assert forall |s: ClusterState| #[trigger] vsts_guarantee(s) implies rmq_rely_vsts(s) by {
                    assert forall |msg| #[trigger] s.in_flight().contains(msg)
                        && msg.content is APIRequest
                        && msg.src.is_controller_id(VStatefulSetReconciler::id())
                        implies (match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => rely_create_req(req),
                            APIRequest::UpdateRequest(req) => rely_update_req(req)(s),
                            APIRequest::GetThenUpdateRequest(req) => rely_get_then_update_req(req)(s),
                            APIRequest::DeleteRequest(req) => rely_delete_req(req)(s),
                            APIRequest::GetThenDeleteRequest(req) => rely_get_then_delete_req(req)(s),
                            APIRequest::UpdateStatusRequest(req) => rely_update_status_req(req)(s),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(vsts_guarantee_create_req(req));
                                // VSTS creates only PodKind or PVCKind; neither is rmq-managed
                                assert(req.obj.kind == Kind::PodKind || req.obj.kind == Kind::PersistentVolumeClaimKind);
                                assert(!is_rmq_managed_kind(req.obj.kind));
                            }
                            APIRequest::GetThenUpdateRequest(req) => {
                                assert(vsts_guarantee_get_then_update_req(req));
                                // VSTS only updates PodKind, not rmq-managed
                                assert(req.obj.kind == Kind::PodKind);
                                assert(!is_rmq_managed_kind(req.obj.kind));
                            }
                            APIRequest::GetThenDeleteRequest(req) => {
                                assert(vsts_guarantee_get_then_delete_req(req));
                                // VSTS only deletes PodKind, not rmq-managed
                                assert(req.key.kind == Kind::PodKind);
                                assert(!is_rmq_managed_kind(req.key.kind));
                            }
                            _ => {}
                        }
                    };
                };
            }
            assert(spec.entails(always(lift_state(vsts_guarantee)))) by {
                vsts_id_ne_vrs_id();
                vsts_id_ne_vd_id();
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
                            APIRequest::UpdateRequest(req) => vsts_rely_mod::rely_update_req(req),
                            APIRequest::GetThenUpdateRequest(req) => vsts_rely_mod::rely_get_then_update_req(req),
                            APIRequest::DeleteRequest(req) => vsts_rely_mod::rely_delete_req(req),
                            APIRequest::GetThenDeleteRequest(req) => vsts_rely_mod::rely_get_then_delete_req(req),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(rmq_guarantee_create_req(req));
                                // RMQ creates rmq-managed kinds (not Pod or PVC)
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
                            APIRequest::CreateRequest(req) => rely_create_req(req),
                            APIRequest::UpdateRequest(req) => rely_update_req(req)(s),
                            APIRequest::GetThenUpdateRequest(req) => rely_get_then_update_req(req)(s),
                            APIRequest::DeleteRequest(req) => rely_delete_req(req)(s),
                            APIRequest::GetThenDeleteRequest(req) => rely_get_then_delete_req(req)(s),
                            APIRequest::UpdateStatusRequest(req) => rely_update_status_req(req)(s),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(vrs_guarantee_create_req(req)(s));
                                assert(req.obj.kind == Kind::PodKind);
                            }
                            APIRequest::GetThenDeleteRequest(req) => {
                                assert(vrs_guarantee_get_then_delete_req(req)(s));
                                assert(req.key.kind == Kind::PodKind);
                            }
                            _ => {}
                        }
                    };
                };
            }
            assert(spec.entails(always(lift_state(vrs_guar)))) by {
                vrs_id_ne_vd_id();
                vsts_id_ne_vrs_id();
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
                            APIRequest::CreateRequest(req) => rely_create_req(req),
                            APIRequest::UpdateRequest(req) => rely_update_req(req)(s),
                            APIRequest::GetThenUpdateRequest(req) => rely_get_then_update_req(req)(s),
                            APIRequest::DeleteRequest(req) => rely_delete_req(req)(s),
                            APIRequest::GetThenDeleteRequest(req) => rely_get_then_delete_req(req)(s),
                            APIRequest::UpdateStatusRequest(req) => rely_update_status_req(req)(s),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(vd_guarantee_create_req(req)(s));
                                assert(req.obj.kind == VReplicaSetView::kind());
                            }
                            APIRequest::GetThenUpdateRequest(req) => {
                                assert(vd_guarantee_get_then_update_req(req)(s));
                                assert(req.obj.kind == VReplicaSetView::kind());
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
                vrs_id_ne_vd_id();
                vsts_id_ne_vd_id();
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
                            APIRequest::GetThenUpdateStatusRequest(req) => vd_rely_get_then_update_status_req(req)(s),
                            APIRequest::DeleteRequest(req) => vd_rely_delete_req(req)(s),
                            APIRequest::GetThenDeleteRequest(req) => vd_rely_get_then_delete_req(req)(s),
                            _ => true,
                        }) by {
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(rmq_guarantee_create_req(req));
                                assert(is_rmq_managed_kind(req.obj.kind));
                                // VReplicaSetView::kind() is a custom resource kind, not rmq-managed
                                assert(req.obj.kind != VReplicaSetView::kind());
                            }
                            APIRequest::UpdateRequest(req) => {
                                assert(rmq_guarantee_update_req(req));
                                assert(is_rmq_managed_kind(req.obj.kind));
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
    proof fn liveness_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_guarantee),
    {
        assert(spec.entails(vsts_spec::next_with_wf(cluster, Self::id()))) by {
            entails_trans(spec, next_with_wf(cluster, Self::id()), vsts_spec::next_with_wf(cluster, Self::id()));
        }

        assert forall |rmq: RabbitmqClusterView| spec.entails(always(lift_state(#[trigger] Cluster::desired_state_is(rmq))).leads_to(always(lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq))))) by {
            rmq_esr_holds_per_cr(spec, rmq, cluster, Self::id());
            assert(spec.entails(rmq_eventually_stable_reconciliation_per_cr(rmq)));

            let rv = choose |rv: ResourceVersion| rmq_eventually_stable_cm_rv(spec, rmq, rv);
            assert(rmq_eventually_stable_cm_rv(spec, rmq, rv));

            let desired_sts = make_stateful_set(rmq, int_to_string_view(rv));

            leads_to_always_combine(
                spec,
                always(lift_state(Cluster::desired_state_is(rmq))),
                lift_state(current_state_matches::<RabbitmqMaker>(rmq)),
                lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))
            );

            assert(lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).entails(lift_state(Cluster::desired_state_is(desired_sts)))) by {
                assert forall |ex: Execution<ClusterState>|
                    lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).satisfied_by(ex)
                    implies #[trigger] lift_state(Cluster::desired_state_is(desired_sts)).satisfied_by(ex) by {
                    let s = ex.head();
                    assert(resource_state_matches::<RabbitmqMaker>(SubResource::StatefulSet, rmq, s));
                    assert(config_map_rv_match::<RabbitmqMaker>(rmq, rv)(s));
                };
            };

            entails_preserved_by_always(
                lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))),
                lift_state(Cluster::desired_state_is(desired_sts))
            );
            entails_implies_leads_to(
                spec,
                always(lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv)))),
                always(lift_state(Cluster::desired_state_is(desired_sts)))
            );
            leads_to_trans(
                spec,
                always(lift_state(Cluster::desired_state_is(rmq))),
                always(lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv)))),
                always(lift_state(Cluster::desired_state_is(desired_sts)))
            );

            let current_state_matches_vsts = |vsts: VStatefulSetView| vsts_liveness_theorem::current_state_matches(vsts);
            assert(spec.entails(Cluster::eventually_stable_reconciliation(current_state_matches_vsts)));
            assert(spec.entails(tla_forall(|vsts: VStatefulSetView| always(lift_state(Cluster::desired_state_is(vsts))).leads_to(always(lift_state(current_state_matches_vsts(vsts)))))));
            use_tla_forall(spec, |vsts: VStatefulSetView| always(lift_state(Cluster::desired_state_is(vsts))).leads_to(always(lift_state(current_state_matches_vsts(vsts)))), desired_sts);

            leads_to_trans(
                spec,
                always(lift_state(Cluster::desired_state_is(rmq))),
                always(lift_state(Cluster::desired_state_is(desired_sts))),
                always(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))
            );

            leads_to_always_combine(
                spec,
                always(lift_state(Cluster::desired_state_is(rmq))),
                lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))),
                lift_state(vsts_liveness_theorem::current_state_matches(desired_sts))
            );

            assert(
                lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))
                .entails(lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq)))
            ) by {
                assert forall |ex: Execution<ClusterState>|
                    lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts))).satisfied_by(ex)
                    implies #[trigger] lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq)).satisfied_by(ex) by {
                    let s = ex.head();
                    assert(config_map_rv_match::<RabbitmqMaker>(rmq, rv)(s));
                    assert(composed_vsts_match::<RabbitmqMaker>(rmq)(s));
                };
            };

            entails_preserved_by_always(
                lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts))),
                lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq))
            );
            entails_implies_leads_to(
                spec,
                always(lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))),
                always(lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq)))
            );
            leads_to_trans(
                spec,
                always(lift_state(Cluster::desired_state_is(rmq))),
                always(lift_state(current_state_matches::<RabbitmqMaker>(rmq)).and(lift_state(config_map_rv_match::<RabbitmqMaker>(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))),
                always(lift_state(composed_current_state_matches::<RabbitmqMaker>(rmq)))
            );
        }
        let composed_current_state_matches = |rmq: RabbitmqClusterView| composed_current_state_matches::<RabbitmqMaker>(rmq);
        spec_entails_tla_forall(spec, |rmq: RabbitmqClusterView| always(lift_state(Cluster::desired_state_is(rmq))).leads_to(always(lift_state(composed_current_state_matches(rmq)))));
        assert(spec.entails(rmq_composed_eventually_stable_reconciliation()));
    }

    proof fn liveness_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_rely),
    {
        assert(Self::composed().contains_key(VStatefulSetReconciler::id())); // trigger
        vsts_id_ne_vrs_id();
        vsts_id_ne_vd_id();
    }
}

}
