use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::*},
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::*, rely_guarantee::*},
    model::{install::*, reconciler::*},
    proof::{predicate::*, liveness::api_actions::*, helper_lemmas::*, helper_invariants},
    proof::liveness::rolling_update::predicate::*,
    proof::liveness::rolling_update::composition::*,
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{seq_lib::*, set_lib::*};
use vstd::{seq_lib::*, map_lib::*, multiset::*};
use vstd::prelude::*;

verus !{

pub proof fn lemma_from_list_resp_with_nv_to_next_state(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, resp_msg: Message, nv_uid_key_replicas_status: (Uid, ObjectRef, int, Option<int>)
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(vd.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s),
    resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, resp_msg)(s),
    new_vrs_and_no_old_vrs_from_resp_objs(vd, controller_id, resp_msg, nv_uid_key_replicas_status)(s),
ensures
    etcd_state_is(vd, controller_id, Some((nv_uid_key_replicas_status.0, nv_uid_key_replicas_status.1, nv_uid_key_replicas_status.2)), 0)(s) ==> local_state_is_valid_and_coherent_with_etcd(vd, controller_id)(s_prime),
    if nv_uid_key_replicas_status.3 is Some && (nv_uid_key_replicas_status.3->0 == nv_uid_key_replicas_status.2) && nv_uid_key_replicas_status.2 != vd.spec.replicas.unwrap_or(int1!()) { // mismatch_replicas
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterScaleNewVRS])(s_prime)
        &&& local_state_is(vd, controller_id, Some((nv_uid_key_replicas_status.0, nv_uid_key_replicas_status.1,
                if nv_uid_key_replicas_status.2 > vd.spec.replicas.unwrap_or(1) {nv_uid_key_replicas_status.2 + 1} else {nv_uid_key_replicas_status.2 - 1}
            )), 0)(s_prime)
        &&& ru_pending_scale_new_vrs_by_one_req_in_flight(vd, controller_id, (nv_uid_key_replicas_status.0, nv_uid_key_replicas_status.1))(s_prime)
    } else {
        &&& at_vd_step_with_vd(vd, controller_id, at_step![AfterEnsureNewVRS])(s_prime)
        &&& local_state_is(vd, controller_id, Some((nv_uid_key_replicas_status.0, nv_uid_key_replicas_status.1, nv_uid_key_replicas_status.2)), 0)(s_prime)
        &&& no_pending_req_in_cluster(vd, controller_id)(s_prime)
    }
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();
    broadcast use group_seq_properties;
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    assert(objects_to_vrs_list(resp_objs) is Some);
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = objects_to_vrs_list(resp_objs)->0.filter(|vrs| valid_owned_vrs(vrs, vd));
    let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
    let new_vrs_uid = Some(nv_uid_key_replicas_status.0);
    let valid_owned_vrs_filter = |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd);
    let managed_vrs_list = vrs_list.filter(valid_owned_vrs_filter);
    assert(new_vrs_or_none is Some);
    let new_vrs = new_vrs_or_none->0;
    assert forall |vrs| #[trigger] vrs_list.contains(vrs) implies vrs.metadata.uid is Some by {
        let i = choose |i: int| 0 <= i < vrs_list.len() && vrs_list[i] == vrs;
        VReplicaSetView::marshal_preserves_metadata();
        assert(resp_objs.contains(resp_objs[i])); // trigger
        assert(VReplicaSetView::unmarshal(resp_objs[i]) is Ok);
        assert(vrs_list[i] == VReplicaSetView::unmarshal(resp_objs[i])->Ok_0);
    }
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies vrs.metadata.uid is Some by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, valid_owned_vrs_filter);
    }
    let old_vrs_list_filter_with_new_vrs = |vrs: VReplicaSetView| {
        &&& new_vrs_or_none is None || vrs.metadata.uid != new_vrs.metadata.uid
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    let another_filter_used_in_esr = |vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    assert(old_vrs_list == managed_vrs_list.filter(old_vrs_list_filter_with_new_vrs));
    // because in reconciler we don't know all objects has uid, which is guaranteed by cluster env predicates
    // so the filter in reconciler didn't use uid->0
    assert(managed_vrs_list.filter(old_vrs_list_filter_with_new_vrs) == managed_vrs_list.filter(another_filter_used_in_esr)) by {
        assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies
            (old_vrs_list_filter_with_new_vrs(vrs) == another_filter_used_in_esr(vrs)) by {
            assert(vrs.metadata.uid is Some);
            assert(new_vrs_uid is Some);
            assert(new_vrs.metadata.uid == new_vrs_uid);
        }
        same_filter_implies_same_result(managed_vrs_list, old_vrs_list_filter_with_new_vrs, another_filter_used_in_esr);
    }
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies vrs_list.contains(vrs) && valid_owned_vrs(vrs, vd) by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, valid_owned_vrs_filter);
    }
    assert forall |vrs: VReplicaSetView| #[trigger] old_vrs_list.contains(vrs) implies
        vrs_list.contains(vrs) && valid_owned_vrs(vrs, vd) && s.resources().contains_key(vrs.object_ref()) by {
        seq_filter_is_a_subset_of_original_seq(managed_vrs_list, old_vrs_list_filter_with_new_vrs);
    }
    assert(managed_vrs_list.contains(new_vrs) && vrs_list.contains(new_vrs) && valid_owned_vrs(new_vrs, vd) && match_template_without_hash(vd.spec.template)(new_vrs)) by {
        assert(managed_vrs_list.contains(new_vrs) && match_template_without_hash(vd.spec.template)(new_vrs)) by { // trigger
            // unwrap filter_old_and_new_vrs
            let non_zero_replicas_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
            if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).len() > 0 {
                seq_filter_is_a_subset_of_original_seq(managed_vrs_list, match_template_without_hash(vd.spec.template));
                if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(non_zero_replicas_filter).len() > 0 {
                    assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(non_zero_replicas_filter).contains(new_vrs));
                    seq_filter_is_a_subset_of_original_seq(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)), non_zero_replicas_filter);
                }
                assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).contains(new_vrs));
            } else {
                assert(new_vrs_or_none is None);
                assert(false);
            }
        }
    };
    let map_key = |vrs: VReplicaSetView| vrs.object_ref();
    assert(old_vrs_list.map_values(map_key).no_duplicates()) by { // triggering_cr.well_formed()
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
        lemma_no_duplication_in_resp_objs_implies_no_duplication_in_down_stream(triggering_cr, resp_objs);
    }
    assert(old_vrs_list.map_values(map_key).to_set()
        == filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s))) by {
        lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, new_vrs_uid, s);
    }
    assert(old_vrs_list.len() == 0) by {
        old_vrs_list.map_values(map_key).unique_seq_to_set();
        assert(old_vrs_list.map_values(map_key).len() == old_vrs_list.len());
        assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s)).len() == 0);
    }

    let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    assert(vds_prime.old_vrs_list == old_vrs_list);
    assert(vds_prime.old_vrs_index == old_vrs_list.len());

    // prove local_state_is_coherent_with_etcd_valid_and_coherent(s_prime)
    assert forall |i| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_index
        implies managed_vrs_list.contains(vds_prime.old_vrs_list[i]) by {
        assert(old_vrs_list.contains(vds_prime.old_vrs_list[i])); // trigger
    }
}

}