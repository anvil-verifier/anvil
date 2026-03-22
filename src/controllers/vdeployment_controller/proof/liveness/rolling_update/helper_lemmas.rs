// helper lemmas just for rolling update
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_invariants, predicate::*, helper_lemmas::*},
    trusted::{rely_guarantee::*, spec_types::*, util::*, liveness_theorem::*, step::VDeploymentReconcileStepView::*},
    proof::liveness::rolling_update::predicate::*,
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*, string_view::*};
use vstd::{seq_lib::*, map_lib::*, set_lib::*};
use vstd::prelude::*;

verus !{

// after inductive csm, the new vrs has > 0 replicas, thus the choice is deterministic
pub proof fn inductive_current_state_matches_implies_filter_old_and_new_vrs_from_resp_objs(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, msg: Message, new_vrs_key: ObjectRef, s: ClusterState
) -> (nv_uid_key_replicas_status: (Uid, ObjectRef, int, Option<int>))
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    // can use ESR instead, so if the witness matches or not doesn't matter
    current_state_matches_with_new_vrs_key(vd, new_vrs_key)(s),
    resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg)(s),
    s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    Cluster::etcd_objects_have_unique_uids()(s),
ensures
    vd.spec.replicas.unwrap_or(1) > 0 ==> nv_uid_key_replicas_status.2 > 0,
    // nv_uid_key_replicas.1 (controller's choice) can be different from new_vrs_key when both vd and new_vrs have 0 replicas
    nv_uid_key_replicas_status.1 != new_vrs_key ==> nv_uid_key_replicas_status.2 == 0 && vd.spec.replicas.unwrap_or(1) == 0,
    new_vrs_and_no_old_vrs_from_resp_objs(vd, controller_id, msg, nv_uid_key_replicas_status, new_vrs_key)(s),
{
    lemma_esr_equiv_to_instantiated_etcd_state_is_with_nv_key(
        vd, cluster, controller_id, new_vrs_key, s
    );
    let resp_objs = msg.content.get_list_response().res.unwrap();
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
    let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
    let nonempty_vrs_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
    let key_map = |vrs: VReplicaSetView| vrs.object_ref();
    VReplicaSetView::marshal_preserves_integrity();
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies {
        &&& vrs.metadata.name is Some
        &&& vrs.metadata.uid is Some
        &&& vrs.metadata.namespace is Some
    } by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, |vrs| valid_owned_vrs(vrs, vd));
        assert(exists |i| 0 <= i < vrs_list.len() && #[trigger] vrs_list[i] == vrs);
        let i = choose |i| 0 <= i < vrs_list.len() && #[trigger] vrs_list[i] == vrs;
        assert(resp_objs.contains(resp_objs[i])); // trigger
        assert(vrs_list == resp_objs.map_values(|o| VReplicaSetView::unmarshal(o)->Ok_0));
        assert(vrs_list[i] == VReplicaSetView::unmarshal(resp_objs[i])->Ok_0);
        VReplicaSetView::marshal_preserves_metadata();
    }
    if new_vrs_or_none is None { // prove contradiction
        assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).len() == 0);
        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(managed_vrs_list, match_template_without_hash(vd.spec.template));
        if exists |k: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(k)
            &&& valid_owned_obj_key(vd, s)(k)
            &&& filter_new_vrs_keys(vd.spec.template, s)(k)
        }{
            let k = choose |k: ObjectRef| {
                &&& #[trigger] s.resources().contains_key(k)
                &&& valid_owned_obj_key(vd, s)(k)
                &&& filter_new_vrs_keys(vd.spec.template, s)(k)
            };
            assert(filter_obj_keys_managed_by_vd(vd, s).contains(k));
            assert(managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).contains(k));
            let i = choose |i: int| 0 <= i < managed_vrs_list.len() && #[trigger] managed_vrs_list.map_values(key_map)[i] == k;
            let vrs = managed_vrs_list[i];
            assert(vrs.object_ref() == k);
            assert(managed_vrs_list.contains(vrs)); // trigger
            assert(false) by {
                assert(!match_template_without_hash(vd.spec.template)(vrs));
                assert(match_template_without_hash(vd.spec.template)(vrs)) by {
                    let etcd_obj = s.resources()[k];
                    let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                    assert(match_template_without_hash(vd.spec.template)(etcd_vrs));
                    assert(etcd_vrs.spec == vrs.spec);
                }
            }
        }
    }
    assert(new_vrs_or_none is Some);
    let new_vrs = new_vrs_or_none->0;
    let new_vrs_uid = Some(new_vrs.metadata.uid->0);
    let uid_of_vrs_with_nv_key = s.resources()[new_vrs_key].metadata.uid->0;
    let vrs_with_nv_key = VReplicaSetView::unmarshal(s.resources()[new_vrs_key])->Ok_0;
    let old_vrs_filter = |vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    assert(managed_vrs_list.contains(new_vrs)) by { // trigger
        seq_filter_is_a_subset_of_original_seq(managed_vrs_list, match_template_without_hash(vd.spec.template));
        if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).len() > 0 {
            seq_filter_is_a_subset_of_original_seq(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)), nonempty_vrs_filter); 
        }
    }
    assert(old_vrs_list == managed_vrs_list.filter(old_vrs_filter)) by {
        same_filter_implies_same_result(managed_vrs_list, old_vrs_filter, |vrs: VReplicaSetView| {
            &&& new_vrs_or_none is None || vrs.metadata.uid != new_vrs_or_none->0.metadata.uid
            &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
        });
    }
    if new_vrs.object_ref() == new_vrs_key {
        assert(new_vrs.metadata.uid->0 == uid_of_vrs_with_nv_key);
        assert(old_vrs_list.len() == 0) by {
            let map_key = |vrs: VReplicaSetView| vrs.object_ref();
            assert(old_vrs_list.len() == old_vrs_list.map_values(map_key).len());
            // this part can be deduped if we move this condition to resp_msg_is_ok_list_resp_containing_matched_vrs
            assert(old_vrs_list.map_values(map_key).no_duplicates()) by {
                lemma_no_duplication_in_resp_objs_implies_no_duplication_in_down_stream(vd, resp_objs);
            }
            old_vrs_list.map_values(map_key).unique_seq_to_set();
            lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, new_vrs_uid, s);
            assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s)).len() == 0);
        }
    } else {
        if new_vrs.spec.replicas.unwrap_or(1) > 0 {
            assert(new_vrs.metadata.uid->0 != uid_of_vrs_with_nv_key);
            assert(managed_vrs_list.contains(new_vrs)); // trigger
            assert(managed_vrs_list.filter(|vrs: VReplicaSetView| {
                &&& Some(uid_of_vrs_with_nv_key) is None || vrs.metadata.uid->0 != Some(uid_of_vrs_with_nv_key)->0
                &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
            }).contains(new_vrs));
            lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, Some(uid_of_vrs_with_nv_key), s);
            assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(uid_of_vrs_with_nv_key), s)).len() == 0);
            // thus contradict with etcd_state_is(.., 0)
            assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(uid_of_vrs_with_nv_key), s)).contains(new_vrs.object_ref()));
            assert(false);
        }
        if vrs_with_nv_key.spec.replicas.unwrap_or(1) > 0 {
            // vrs with nv_uid_key can pass the nonempty_vrs_filter, it's impossible for new_vrs to be selected here
            assert(new_vrs.metadata.uid->0 != uid_of_vrs_with_nv_key);
            assert(valid_owned_obj_key(vd, s)(new_vrs.object_ref()));
            assert(filter_obj_keys_managed_by_vd(vd, s).contains(new_vrs_key));
            assert(managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).contains(new_vrs_key));
            let i = choose |i: int| 0 <= i < managed_vrs_list.len() && #[trigger] managed_vrs_list.map_values(key_map)[i] == new_vrs_key;
            let vrs = managed_vrs_list[i];
            assert(vrs.object_ref() == new_vrs_key);
            assert(managed_vrs_list.contains(vrs)); // trigger
            assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).contains(vrs)) by {
                assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).contains(vrs)); // trigger
            }
            assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).len() > 0);
            assert(!managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).contains(new_vrs));
            assert(false);
        }
    }
    if vd.spec.replicas == Some(int0!()) && new_vrs.spec.replicas == Some(int0!()) && new_vrs.object_ref() != new_vrs_key { // new_vrs can pass nonempty_vrs_filter and old_vrs_filter
        assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).len() == 0);
        // vrs with new_vrs_key must has 0 replicas
        if old_vrs_list.len() > 0 {
            let havoc_vrs = old_vrs_list[0];
            assert(old_vrs_list.contains(havoc_vrs));
            seq_filter_contains_implies_seq_contains(managed_vrs_list, old_vrs_filter, havoc_vrs);
            assert(havoc_vrs.spec.replicas.unwrap_or(1) > 0);
            if havoc_vrs.object_ref() == new_vrs_key {
                assert(vrs_with_nv_key.spec.replicas.unwrap_or(1) > 0);
                let vrs_with_nv_key = choose |vrs| #[trigger] managed_vrs_list.contains(vrs) && vrs.object_ref() == new_vrs_key;
                assert(vrs_with_nv_key.spec.replicas.unwrap_or(1) > 0);
                assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).contains(vrs_with_nv_key));
                assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).contains(vrs_with_nv_key));
                assert(false);
            }
            assert(managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).to_set().contains(new_vrs.object_ref()));
            assert(s.resources().contains_key(havoc_vrs.object_ref()));
            assert(false);
        }
    }
    assert(new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd, controller_id, msg, Some((new_vrs.metadata.uid->0, new_vrs.object_ref(), new_vrs.spec.replicas.unwrap_or(1))), nat0!())(s));
    assert((|nv_uid_key_replicas: (Uid, ObjectRef, int)| new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd, controller_id, msg, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, nv_uid_key_replicas.2)), nat0!())(s))(
        (new_vrs_uid->0, new_vrs.object_ref(), new_vrs.spec.replicas.unwrap_or(1))
    ));
    let status_replicas = if new_vrs.status is Some {
        Some(new_vrs.status->0.replicas)
    } else {
        None
    };
    return (new_vrs_uid->0, new_vrs.object_ref(), new_vrs.spec.replicas.unwrap_or(1), status_replicas);
}

    
}