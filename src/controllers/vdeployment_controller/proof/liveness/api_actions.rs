use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::*},
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::*, rely_guarantee::*},
    model::{install::*, reconciler::*},
    proof::{predicate::*, helper_invariants, helper_lemmas::*},
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use vstd::{seq_lib::*, prelude::*, map_lib::*, set::*};
use crate::vstd_ext::{seq_lib::*, set_lib::*, map_lib::*};

verus! {

#[verifier(rlimit(10))]
pub proof fn lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    req_msg: Message,
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_list_vrs_req(vd, controller_id, req_msg, s),
    at_vd_step_with_vd(vd, controller_id, at_step![AfterListVRS])(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    Cluster::etcd_is_finite()(s_prime),
ensures
    resp_msg == handle_list_request_msg(req_msg, s.api_server).1,
    resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s_prime),
{
    broadcast use group_seq_properties;
    VReplicaSetView::marshal_preserves_integrity();
    let req = req_msg.content.get_list_request();
    let list_req_filter = |o: DynamicObjectView| {
        // why changing the order of fields makes a difference
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
    }; 
    let resp_msg = handle_list_request_msg(req_msg, s.api_server).1;
    assert(resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s_prime)) by {
        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
        assert(resp_objs == s.resources().values().filter(list_req_filter).to_seq());
        assert forall |o| #[trigger] resp_objs.contains(o) implies {
            &&& o.kind == VReplicaSetView::kind()
            &&& VReplicaSetView::unmarshal(o) is Ok
            &&& s_prime.resources().contains_key(o.object_ref())
            &&& s_prime.resources()[o.object_ref()] == o
            &&& o.metadata.namespace is Some
            &&& o.metadata.name is Some
            &&& o.metadata.uid is Some
        } by {
            assert(s.resources().values().filter(list_req_filter).contains(o)) by {
                lemma_values_finite(s.resources());
                finite_set_to_seq_contains_all_set_elements(s.resources().values().filter(list_req_filter));
            }
        }
        assert(objects_to_vrs_list(resp_objs) is Some) by {
            seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(resp_objs, |o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err());
        }
        assert(resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates()) by {
            lemma_values_finite(s.resources());
            finite_set_to_seq_has_no_duplicates(s.resources().values().filter(list_req_filter));
            // now we know resp_objs has no duplicates, prove keys are unique by contradiction
            assert forall|i, j| (0 <= i < resp_objs.len() && 0 <= j < resp_objs.len() && i != j) implies #[trigger] resp_objs[i].object_ref() != #[trigger] resp_objs[j].object_ref() by {
                if resp_objs[i].object_ref() == resp_objs[j].object_ref() {
                    // trigger of s.resources()[o.object_ref()] == o
                    assert(resp_objs.contains(resp_objs[i]));
                    assert(resp_objs.contains(resp_objs[j]));
                    assert(resp_objs[i] == resp_objs[j]);
                }
            }
        }
        let vrs_list = objects_to_vrs_list(resp_objs)->0;
        assert(vrs_list == resp_objs.map_values(|o: DynamicObjectView| VReplicaSetView::unmarshal(o)->Ok_0));
        let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
        assert forall |vrs: VReplicaSetView| #[trigger] managed_vrs_list.contains(vrs) implies  {
            let key = vrs.object_ref();
            let etcd_obj = s.resources()[key];
            let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
            // strengthen valid_owned_vrs, as only one controller owner is allowed
            &&& vrs.metadata.owner_references is Some
            &&& vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
            &&& valid_owned_vrs(vrs, vd)
            &&& s.resources().contains_key(key)
            &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
            // weakly equal to etcd object
            &&& valid_owned_obj_key(vd, s)(key)
            &&& vrs_weakly_eq(etcd_vrs, vrs)
            &&& etcd_vrs.spec == vrs.spec
        } by {
            VReplicaSetView::marshal_preserves_metadata();
            let key = vrs.object_ref();
            let etcd_obj = s.resources()[key];
            let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
            seq_filter_contains_implies_seq_contains(vrs_list, |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd), vrs);
            let i = choose |i| 0 <= i < vrs_list.len() && vrs_list[i] == vrs;
            assert(resp_objs.contains(resp_objs[i])); // trigger
            assert(VReplicaSetView::unmarshal(resp_objs[i])->Ok_0 == vrs);
            assert(vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
                assert(vrs.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
            }
        }
        // expand to 
        // assert(s.resources().values().filter(list_req_filter).to_seq().map_values(|o: DynamicObjectView| VReplicaSetView::unmarshal(o)->Ok_0).filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd)).map_values(|vrs: VReplicaSetView| vrs.object_ref()).to_set()
        //        == s.resources().dom().filter(valid_owned_obj_key(vd, s)))
        assert(managed_vrs_list.map_values((|vrs: VReplicaSetView| vrs.object_ref())).to_set() == filter_obj_keys_managed_by_vd(vd, s_prime)) by {
            let valid_obj_filter = |o: DynamicObjectView| {
                &&& o.kind == VReplicaSetView::kind()
                &&& VReplicaSetView::unmarshal(o) is Ok
                &&& valid_owned_vrs(VReplicaSetView::unmarshal(o)->Ok_0, vd)
            };
            let weakened_obj_filter = |o: DynamicObjectView| {
                &&& valid_owned_vrs(VReplicaSetView::unmarshal(o)->Ok_0, vd)
            };
            assert(filter_obj_keys_managed_by_vd(vd, s_prime) == s_prime.resources().values().filter(valid_obj_filter).map(|o: DynamicObjectView| o.object_ref())) by {
                assert(forall |k: ObjectRef| #[trigger] s_prime.resources().contains_key(k) ==>
                    valid_owned_obj_key(vd, s_prime)(k) == valid_obj_filter(s_prime.resources()[k]));
                lemma_equiv_filters_on_keys_and_values_implies_equiv_results(s_prime.resources(), valid_owned_obj_key(vd, s_prime), valid_obj_filter, |o: DynamicObjectView| o.object_ref());
            }
            assert(managed_vrs_list == resp_objs.filter(weakened_obj_filter).map_values(|o: DynamicObjectView| VReplicaSetView::unmarshal(o)->Ok_0)) by {
                commutativity_of_seq_map_and_filter(resp_objs, weakened_obj_filter, |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd), |o: DynamicObjectView| VReplicaSetView::unmarshal(o)->Ok_0);
            }
            // map_values(unmarshal).map_values(object_ref) ==> map_values(object_ref)
            assert(managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()) == resp_objs.filter(weakened_obj_filter).map_values(|o: DynamicObjectView| o.object_ref())) by {
                assert forall |o: DynamicObjectView| #[trigger] resp_objs.filter(weakened_obj_filter).contains(o) implies
                    o.kind == VReplicaSetView::kind() && VReplicaSetView::unmarshal(o) is Ok by {
                    seq_filter_contains_implies_seq_contains(resp_objs, weakened_obj_filter, o);
                }
                lemma_homomorphism_of_map_values(resp_objs.filter(weakened_obj_filter), |o: DynamicObjectView| VReplicaSetView::unmarshal(o)->Ok_0, |vrs: VReplicaSetView| vrs.object_ref(), |o: DynamicObjectView| o.object_ref());
            }
            // s.to_seq().to_set() ==> s
            assert(resp_objs.filter(weakened_obj_filter).map_values(|o: DynamicObjectView| o.object_ref()).to_set()
                == s_prime.resources().values().filter(valid_obj_filter).map(|o: DynamicObjectView| o.object_ref())) by {
                // s.r().v().finite()
                injective_finite_map_implies_dom_len_is_equal_to_values_len(s_prime.resources());
                // .to_seq is not mutable because order isn't guaranteed, so we have to move .to_set() forward to cancel it
                // .m().to_set() == .to_set().m() to get rid of the map
                resp_objs.filter(weakened_obj_filter).lemma_to_set_map_commutes(|o: DynamicObjectView| o.object_ref());
                // .to_seq().f().to_set() == .to_seq().to_set().f() == .f()
                lemma_filter_to_set_eq_to_set_filter(resp_objs, weakened_obj_filter);
                lemma_to_seq_to_set_equal(s_prime.resources().values().filter(list_req_filter));
                // list_req_filter && weakened_obj_filter && (every object in etcd is well-formed) == valid_obj_filter
                assert(s_prime.resources().values().filter(list_req_filter).filter(weakened_obj_filter) == s_prime.resources().values().filter(valid_obj_filter));
            }
            // .values().map(val_to_key) ==> .dom() (keys)
            assert(s_prime.resources().values().filter(valid_obj_filter).map(|o: DynamicObjectView| o.object_ref())
                == s_prime.resources().dom().filter(valid_owned_obj_key(vd, s_prime)));
        }
    }
    return resp_msg;
}

pub proof fn lemma_create_new_vrs_request_returns_ok(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    req_msg: Message, n: nat
) -> (res: (Message, (Uid, ObjectRef)))
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_pending_create_new_vrs_req_in_flight(vd, controller_id, req_msg)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, None, n)(s),
    local_state_is_valid_and_coherent_with_etcd(vd, controller_id)(s),
    s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()),
ensures
    res.0 == handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1,
    resp_msg_matches_req_msg(res.0, req_msg),
    resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, res.0, res.1)(s_prime),
    etcd_state_is(vd, controller_id, Some(((res.1).0, (res.1).1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime),
    filter_obj_keys_managed_by_vd(vd, s_prime).filter(filter_old_vrs_keys(Some((res.1).0), s_prime))
        == filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(None, s)),
    // created obj has different key and uid from all old_vrs in local_state
    ({
        let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        // TODO: only talk about keys and uids on API server side, may need to update local_state_is_valid_and_coherent_with_etcd to include uid
        &&& forall |i| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_list.len() ==>
            vds_prime.old_vrs_list[i].metadata.uid->0 != (res.1).0 && vds_prime.old_vrs_list[i].object_ref() != (res.1).1
    }),
{
    broadcast use group_seq_properties;
    VReplicaSetView::marshal_preserves_integrity();
    VDeploymentView::marshal_preserves_integrity();
    // VReplicaSetView::marshal_spec_preserves_integrity();
    let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    let req = req_msg.content.get_APIRequest_0().get_CreateRequest_0();
    let new_vrs = lemma_make_replica_set_passes_match_template_without_hash(triggering_cr); // vd doesn't have rv
    assert(match_template_without_hash(vd.spec.template)(new_vrs));
    assert(req == CreateRequest {
        namespace: vd.metadata.namespace.unwrap(),
        obj: new_vrs.marshal()
    });
    assert(s_prime.api_server == handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).0);
    let resp_msg = handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1;
    let resp_obj = resp_msg.content.get_create_response().res.unwrap();
    let key = resp_obj.object_ref();
    // emulate handle_create_request
    let created_obj = DynamicObjectView {
        kind: req.obj.kind,
        metadata: ObjectMetaView {
            name: Some(generate_name(s.api_server)),
            namespace: Some(req.namespace),
            resource_version: Some(s.api_server.resource_version_counter),
            uid: Some(s.api_server.uid_counter),
            deletion_timestamp: None,
            ..req.obj.metadata
        },
        spec: req.obj.spec,
        status: marshalled_default_status(req.obj.kind, cluster.installed_types), // Overwrite the status with the default one
    };
    assert(!s.resources().contains_key(created_obj.object_ref())) by {
        assert(created_obj.object_ref().name == generate_name(s.api_server));
        generated_name_is_unique(s.api_server);
        if s.resources().contains_key(created_obj.object_ref()) {
            assert(false);
        }
    }
    assert(created_object_validity_check(created_obj, cluster.installed_types) is None) by {
        assert(metadata_validity_check(created_obj) is None) by {
            assert(created_obj.metadata.owner_references is Some);
            assert(created_obj.metadata.owner_references->0.len() == 1);
        }
    }
    assert(resp_obj == created_obj);
    assert(s_prime.resources() == s.resources().insert(key, resp_obj));
    let vrs = VReplicaSetView::unmarshal(resp_obj)->Ok_0;
    assert(resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, resp_msg, (created_obj.metadata.uid->0, key))(s_prime)) by {
        VReplicaSetView::marshal_preserves_integrity();
        let singleton_seq = seq![vd.controller_owner_ref()];
        assert(singleton_seq == Seq::empty().push(vd.controller_owner_ref()));
        assert(vrs.metadata.owner_references->0.filter(controller_owner_filter()) == singleton_seq) by {
            assert(vrs.metadata.owner_references->0 == singleton_seq);
            lemma_filter_push(Seq::empty(), controller_owner_filter(), vd.controller_owner_ref());
        }
        assert(match_template_without_hash(vd.spec.template)(vrs)) by {
            VReplicaSetView::marshal_spec_preserves_integrity();
            assert(vrs.spec == new_vrs.spec);
        }
        let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        let vds_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
        assert forall |i| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_list.len() implies
            vds_prime.old_vrs_list[i].metadata.uid->0 != created_obj.metadata.uid->0 && vds_prime.old_vrs_list[i].object_ref() != key by {
            assert(s.resources().contains_key(vds_prime.old_vrs_list[i].object_ref())) by {
                assert(s.resources().contains_key(vds.old_vrs_list[i].object_ref()));
            }
            assert(created_obj.metadata.uid->0 == s.api_server.uid_counter); // etcd_object_is_weakly_well_formed
            assert(vds_prime.old_vrs_list[i].object_ref() != key) by {
                generated_name_is_unique(s.api_server);
            }
        }
    }
    // we know the former one's length is n
    assert(filter_obj_keys_managed_by_vd(vd, s_prime).filter(filter_old_vrs_keys(Some(created_obj.metadata.uid->0), s_prime)) == 
        filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(created_obj.metadata.uid->0), s))) by {
        assert(!filter_old_vrs_keys(Some(created_obj.metadata.uid->0), s_prime)(key));
    }
    let replicas_non_zero_filter = |k: ObjectRef| {
        let obj = s.resources()[k];
        let vrs = VReplicaSetView::unmarshal(obj)->Ok_0;
        &&& obj.kind == VReplicaSetView::kind()
        &&& VReplicaSetView::unmarshal(obj) is Ok
        &&& vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0
    };
    let managed_keys_in_s = filter_obj_keys_managed_by_vd(vd, s);
    assert(managed_keys_in_s.filter(filter_old_vrs_keys(Some(created_obj.metadata.uid->0), s)) == managed_keys_in_s.filter(replicas_non_zero_filter));
    assert(managed_keys_in_s.filter(filter_old_vrs_keys(None, s)) == managed_keys_in_s.filter(replicas_non_zero_filter));
    return (resp_msg, (created_obj.metadata.uid->0, key));
}

pub proof fn lemma_scale_new_vrs_req_returns_ok(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    req_msg: Message, nv_uid_key_replicas: (Uid, ObjectRef, int), n: nat
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_pending_scale_new_vrs_req_in_flight(vd, controller_id, req_msg, (nv_uid_key_replicas.0, nv_uid_key_replicas.1))(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, Some(nv_uid_key_replicas), n)(s),
    nv_uid_key_replicas.2 != vd.spec.replicas.unwrap_or(int1!()),
ensures
    resp_msg == handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1,
    resp_msg_is_ok_scale_new_vrs_resp_in_flight(vd, controller_id, resp_msg, (nv_uid_key_replicas.0, nv_uid_key_replicas.1))(s_prime),
    etcd_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime),
    // lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd, but when the msg is from vd controller
    filter_obj_keys_managed_by_vd(vd, s_prime).filter(filter_old_vrs_keys(Some(nv_uid_key_replicas.0), s_prime))
        == filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key_replicas.0), s))
{
    VReplicaSetView::marshal_preserves_integrity();
    let req = req_msg.content.get_get_then_update_request();
    let etcd_obj = s.resources()[req.key()];
    // update can succeed
    assert(etcd_obj.metadata.owner_references_contains(req.owner_ref));
    assert(req.owner_ref == vd.controller_owner_ref());
    assert(s.resources().contains_key(req.key()));
    assert(s_prime.api_server == handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).0);
    let resp_msg = handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1;
    let updated_obj = s_prime.resources()[req.key()];
    let updated_vrs = VReplicaSetView::unmarshal(updated_obj)->Ok_0;

    assert(filter_new_vrs_keys(vd.spec.template, s_prime)(req.key()));

    // assert(filter_obj_keys_managed_by_vd(vd, s_prime) == filter_obj_keys_managed_by_vd(vd, s).insert(key));
    assert(filter_obj_keys_managed_by_vd(vd, s_prime).filter(filter_old_vrs_keys(Some(nv_uid_key_replicas.0), s_prime)) == 
        filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key_replicas.0), s))) by {
        assert(!filter_old_vrs_keys(Some(nv_uid_key_replicas.0), s_prime)(req.key()));
    }

    return resp_msg;
}

pub proof fn lemma_scale_old_vrs_req_returns_ok(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    req_msg: Message, nv_uid_key: (Uid, ObjectRef), n: nat
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_pending_scale_old_vrs_req_in_flight(vd, controller_id, req_msg, nv_uid_key.0)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)(s),
ensures
    resp_msg == handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1,
    resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd, controller_id, resp_msg, nv_uid_key.0)(s_prime),
    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), (n - nat1!()) as nat)(s_prime),
    // lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd, but when the msg is from vd controller
    filter_obj_keys_managed_by_vd(vd, s_prime).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s_prime))
        == filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s)).remove(req_msg.content.get_get_then_update_request().key()),
{
    VReplicaSetView::marshal_preserves_integrity();
    // let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    let req = req_msg.content.get_get_then_update_request();
    let etcd_obj = s.resources()[req.key()];
    // update can succeed
    assert(etcd_obj.metadata.owner_references_contains(req.owner_ref));
    assert(req.owner_ref == vd.controller_owner_ref());
    assert(s_prime.api_server == handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).0);
    let resp_msg = handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1;
    let updated_obj = s_prime.resources()[req.key()];
    let updated_vrs = VReplicaSetView::unmarshal(updated_obj)->Ok_0;

    assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s)).remove(req.key()) == 
        filter_obj_keys_managed_by_vd(vd, s_prime).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s_prime))) by {
        assert(!filter_old_vrs_keys(Some(nv_uid_key.0), s_prime)(req.key())) by {
            assert(updated_vrs.spec.replicas == Some(int0!())) by {
                assert(updated_obj.spec == req.obj.spec);
            }
        }
    }
    assert(filter_obj_keys_managed_by_vd(vd, s_prime).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s_prime)).len() == n - 1) by {
        assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s)).contains(req.key()));
    }
    return resp_msg;
}

pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_local_state_validity_and_coherence(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    forall |vd| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(cluster, controller_id)(s),
    msg.src != HostId::Controller(controller_id, vd.object_ref()),
    s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()),
    local_state_is_valid_and_coherent_with_etcd(vd, controller_id)(s),
ensures
    local_state_is_valid_and_coherent_with_etcd(vd, controller_id)(s_prime),
{
    broadcast use group_seq_properties;
    VReplicaSetView::marshal_preserves_integrity();
    let vds = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let vds_prime = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].local_state).unwrap();
    let (nv_uid_key_replicas, n) = choose |i: (Option<(Uid, ObjectRef, int)>, nat)| #[trigger] local_state_is(vd, controller_id, i.0, i.1)(s);
    assert forall |i| #![trigger vds_prime.old_vrs_list[i]] 0 <= i < vds_prime.old_vrs_list.len()
        implies {
            let key = vds_prime.old_vrs_list[i].object_ref();
            &&& s_prime.resources().contains_key(key)
            &&& s_prime.resources()[key] == s.resources()[key]
            &&& valid_owned_obj_key(vd, s_prime)(key)
        } by {
            lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                s, s_prime, vd, cluster, controller_id, msg
            );
    }
    if vds.new_vrs is Some {
        let obj = s.resources()[vds.new_vrs->0.object_ref()];
        assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
        }
        lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
            s, s_prime, vd, cluster, controller_id, msg
        );
    }
    assert(local_state_is_valid_and_coherent_with_etcd(vd, controller_id)(s_prime));
    
}

pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int,// new_vrs, old_vrs_list
    msg: Message, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    forall |vd| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(cluster, controller_id)(s),
    msg.src != HostId::Controller(controller_id, vd.object_ref()),
    etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)(s),
    // etcd state should be maintained even when vd is not in ongoing_reconciles
    // s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()),
ensures
    etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)(s_prime),
{
    if etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)(s) {
        let nv_uid = match nv_uid_key_replicas {
            Some((uid, _, _)) => Some(uid),
            None => None
        };
        lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
            s, s_prime, vd, cluster, controller_id, msg, nv_uid
        );
        match nv_uid_key_replicas {
            Some((uid, key, replicas)) => {
                let obj = s.resources()[key];
                assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
                    assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
                }
                lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                    s, s_prime, vd, cluster, controller_id, msg
                );
            },
            None => {
                // if no new_vrs exists in s, no new_vrs should exist in s_prime, prove by contradiction
                if exists |k: ObjectRef| {
                    &&& #[trigger] s_prime.resources().contains_key(k)
                    &&& valid_owned_obj_key(vd, s_prime)(k)
                    &&& filter_new_vrs_keys(vd.spec.template, s_prime)(k)
                }{
                    let key = choose |k: ObjectRef| {
                        &&& #[trigger] s_prime.resources().contains_key(k)
                        &&& valid_owned_obj_key(vd, s_prime)(k)
                        &&& filter_new_vrs_keys(vd.spec.template, s_prime)(k)
                    };
                    let obj = s_prime.resources()[key];
                    assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
                        assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
                    }
                    // !p(s) => !p(s') <==> p(s') => p(s), I love this ownership lemma
                    lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                    assert(s.resources().contains_key(key));
                }
            }
        }
    }
}

// equal to etcd_state_is maintained by lemma_esr_equiv_to_instantiated_etcd_state_is
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_current_state_matches(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    forall |vd| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(cluster, controller_id)(s),
    msg.src != HostId::Controller(controller_id, vd.object_ref()),
    current_state_matches(vd)(s),
ensures
    current_state_matches(vd)(s_prime),
{
    assert(instantiated_etcd_state_is_with_zero_old_vrs(vd, controller_id)(s)) by {
        lemma_esr_equiv_to_instantiated_etcd_state_is(vd, cluster, controller_id, s);
    }
    let (uid, key) = choose |nv_uid_key: (Uid, ObjectRef)| {
        &&& #[trigger] etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), 0)(s)
    };
    lemma_api_request_other_than_pending_req_msg_maintains_etcd_state(
        s, s_prime, vd, cluster, controller_id, msg, Some((uid, key, vd.spec.replicas.unwrap_or(1))), nat0!()
    );
    assert(current_state_matches(vd)(s_prime)) by {
        lemma_esr_equiv_to_instantiated_etcd_state_is(vd, cluster, controller_id, s_prime);
    }
}

// filter_obj_keys_managed_by_vd is maintained
// next time, we should unify the filters to use obj or key
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int,
    msg: Message, nv_uid: Option<Uid>
)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    forall |vd| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(cluster, controller_id)(s),
    msg.src != HostId::Controller(controller_id, vd.object_ref()),
    // (!Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg)
    //     || !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())),
ensures
    filter_obj_keys_managed_by_vd(vd, s) == filter_obj_keys_managed_by_vd(vd, s_prime),
    filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(nv_uid, s))
        == filter_obj_keys_managed_by_vd(vd, s_prime).filter(filter_old_vrs_keys(nv_uid, s_prime)),
    s.resources().values() // for current_state_match_vd_applied_to_vrs_set in composition proof
        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
    == s_prime.resources().values()
        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd)),
{
    // ==>
    assert forall |k: ObjectRef| #[trigger] filter_obj_keys_managed_by_vd(vd, s).contains(k) implies {
        &&& filter_obj_keys_managed_by_vd(vd, s_prime).contains(k)
        &&& filter_old_vrs_keys(nv_uid, s)(k) == filter_old_vrs_keys(nv_uid, s_prime)(k)
    } by {
        let obj = s.resources()[k];
        assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
            // each_object_in_etcd_has_at_most_one_controller_owner
            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
        }
        lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
            s, s_prime, vd, cluster, controller_id, msg
        );
    }
    // <==
    assert forall |k: ObjectRef| #[trigger] filter_obj_keys_managed_by_vd(vd, s_prime).contains(k) implies {
        &&& filter_obj_keys_managed_by_vd(vd, s).contains(k)
        &&& filter_old_vrs_keys(nv_uid, s)(k) == filter_old_vrs_keys(nv_uid, s_prime)(k)
     } by {
        let obj = s_prime.resources()[k];
        assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
            // each_object_in_etcd_has_at_most_one_controller_owner
            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
        }
        lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
            s, s_prime, vd, cluster, controller_id, msg
        );
    }
    // ==>
    assert forall |obj: DynamicObjectView| {
        &&& #[trigger] s.resources().values().contains(obj)
        &&& obj.kind == VReplicaSetView::kind()
        &&& valid_owned_vrs(VReplicaSetView::unmarshal(obj)->Ok_0, vd)
    } implies {
        &&& s_prime.resources().values().contains(obj)
    } by {
        assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
            // each_object_in_etcd_has_at_most_one_controller_owner
            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
        }
        lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
            s, s_prime, vd, cluster, controller_id, msg
        );
    }
    // <==
    assert forall |obj: DynamicObjectView| {
        &&& #[trigger] s_prime.resources().values().contains(obj)
        &&& obj.kind == VReplicaSetView::kind()
        &&& valid_owned_vrs(VReplicaSetView::unmarshal(obj)->Ok_0, vd)
    } implies {
        &&& s.resources().values().contains(obj)
    } by {
        assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
            // each_object_in_etcd_has_at_most_one_controller_owner
            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
        }
        lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
            s, s_prime, vd, cluster, controller_id, msg
        );
    }
    let vrs_set = s.resources().values()
        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd));
    let vrs_set_prime = s_prime.resources().values()
        .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
        .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
        .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd));
    assert forall |vrs: VReplicaSetView| #[trigger] vrs_set.contains(vrs) implies vrs_set_prime.contains(vrs) by {
        let obj = choose |obj: DynamicObjectView| #![trigger s.resources().values().contains(obj)] {
            &&& s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(obj)
            &&& VReplicaSetView::unmarshal(obj)->Ok_0 == vrs
        };
        // interestingly, contains() passes from/to filtered set more easily than seq
        assert(s_prime.resources().values().contains(obj)); // trigger
        assert(s_prime.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(obj));
        assert(s_prime.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0).contains(vrs));
    }
    assert forall |vrs: VReplicaSetView| #[trigger] vrs_set_prime.contains(vrs) implies vrs_set.contains(vrs) by {
        let obj = choose |obj: DynamicObjectView| #![trigger s_prime.resources().values().contains(obj)] {
            &&& s_prime.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(obj)
            &&& VReplicaSetView::unmarshal(obj)->Ok_0 == vrs
        };
        assert(s.resources().values().contains(obj)); // trigger
        assert(s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind()).contains(obj));
        assert(s.resources().values().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0).contains(vrs));
    }
}

// This lemma proves for all objects owned by vd (checked by namespace and owner_ref),
// the API req msg does not touch the object as the direct result of rely condition and non-interference property.
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    cluster.each_builtin_object_in_etcd_is_well_formed()(s),
    cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
    Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)(s),
    cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
    Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
    Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id)(s),
    Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)(s),
    Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())(s),
    Cluster::there_is_the_controller_state(controller_id)(s),
    Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref())(s),
    helper_invariants::garbage_collector_does_not_delete_vd_vrs_objects(vd)(s), // still relies on desired_state_is indirectly
    helper_invariants::every_msg_from_vd_controller_carries_vd_key(controller_id)(s),
    helper_invariants::vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)(s),
    helper_invariants::no_pending_mutation_request_not_from_controller_on_vrs_objects()(s),
    forall |vd| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    helper_invariants::no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id)(s),
    vd_rely_condition(cluster, controller_id)(s),
    msg.src != HostId::Controller(controller_id, vd.object_ref()),
    // old style pre, stronger to pre above
    // (!Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg)
    //     || !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())),
ensures
    // ultimate version of ownership and guarantee
    forall |k: ObjectRef| { // ==>
        let obj = s.resources()[k];
        &&& #[trigger] s.resources().contains_key(k)
        &&& VReplicaSetView::unmarshal(obj) is Ok
        &&& obj.metadata.namespace == vd.metadata.namespace
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
    } ==> {
        &&& s_prime.resources().contains_key(k)
        // TODO: weaken to allow status update requests
        &&& s.resources()[k] == s_prime.resources()[k]
    },
    forall |k: ObjectRef| { // <==
        let obj = s_prime.resources()[k];
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& VReplicaSetView::unmarshal(obj) is Ok
        &&& obj.metadata.namespace == vd.metadata.namespace
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
    } ==> {
        &&& s.resources().contains_key(k)
        // TODO: weaken to allow status update requests
        &&& s.resources()[k] == s_prime.resources()[k]
    },
{
    assert forall |k: ObjectRef| { // ==>
        let obj = s.resources()[k];
        &&& #[trigger] s.resources().contains_key(k)
        &&& VReplicaSetView::unmarshal(obj) is Ok
        &&& obj.metadata.namespace == vd.metadata.namespace
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
    } implies {
        &&& s_prime.resources().contains_key(k)
        // TODO: weaken to allow status update requests
        &&& s.resources()[k] == s_prime.resources()[k]
    } by {
        // ==>
        let obj = s.resources()[k];
        VReplicaSetView::marshal_preserves_integrity();
        // trigger rely condition,
        // rule out cases when obj get deleted with rely_delete and handle_delete_eq checks
        assert(obj.metadata.owner_references->0.contains(vd.controller_owner_ref())) by {
            broadcast use group_seq_properties;
            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]);
            seq_filter_contains_implies_seq_contains(obj.metadata.owner_references->0, controller_owner_filter(), vd.controller_owner_ref());
        }
        if msg.content.is_APIRequest() && msg.dst.is_APIServer() {
            match msg.src {
                HostId::Controller(id, cr_key) => {
                    if id == controller_id {
                        assert(cr_key != vd.object_ref());
                        // same controller, other vd
                        // every_msg_from_vd_controller_carries_vd_key
                        let cr_key = msg.src.get_Controller_1();
                        let other_vd = VDeploymentView {
                            metadata: ObjectMetaView {
                                name: Some(cr_key.name),
                                namespace: Some(cr_key.namespace),
                                ..make_vd().metadata
                            },
                            ..make_vd()
                        };
                        // so msg can only be list, create or get_then_update
                        assert(helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, other_vd)(s));
                        match msg.content.get_APIRequest_0() {
                            APIRequest::DeleteRequest(req) => assert(false), // vd controller doesn't send delete req
                            APIRequest::GetThenDeleteRequest(req) => assert(false),
                            APIRequest::GetThenUpdateRequest(req) => {
                                assert(helper_invariants::no_other_pending_get_then_update_request_interferes_with_vd_reconcile(req, vd)(s));
                                assert(helper_invariants::vd_reconcile_get_then_update_request_only_interferes_with_itself(req, other_vd)(s));
                                // controller_owner_ref does not carry namespace, while object_ref does
                                // so object_ref != is not enough to prove controller_owner_ref !=
                                if cr_key.namespace == vd.metadata.namespace->0 {
                                    assert(!obj.metadata.owner_references_contains(req.owner_ref)) by {
                                        if obj.metadata.owner_references_contains(req.owner_ref) {
                                            assert(req.owner_ref != vd.controller_owner_ref());
                                            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                        }
                                    }
                                } // or else, namespace is different, so should not be touched at all
                            },
                            _ => {},
                        }
                        VDeploymentReconcileState::marshal_preserves_integrity();
                    } else {
                        let other_id = msg.src.get_Controller_0();
                        // by every_in_flight_req_msg_from_controller_has_valid_controller_id, used by vd_rely
                        assert(cluster.controller_models.contains_key(other_id));
                        assert(vd_rely(other_id)(s)); // trigger vd_rely_condition
                        VDeploymentReconcileState::marshal_preserves_integrity();
                        match msg.content.get_APIRequest_0() {
                            APIRequest::DeleteRequest(req) => {},
                            APIRequest::GetThenDeleteRequest(req) => {
                                if req.key.kind == VReplicaSetView::kind() {
                                    assert(!obj.metadata.owner_references_contains(req.owner_ref)) by {
                                        if obj.metadata.owner_references_contains(req.owner_ref) {
                                            assert(req.owner_ref != vd.controller_owner_ref());
                                            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                        }
                                    }
                                }
                            },
                            APIRequest::GetThenUpdateRequest(req) => {
                                if req.obj.kind == VReplicaSetView::kind() {
                                    // rely condition
                                    assert({
                                        &&& req.owner_ref.controller is Some
                                        &&& req.owner_ref.controller->0
                                        &&& req.owner_ref.kind != VDeploymentView::kind()
                                    });
                                    assert(!obj.metadata.owner_references_contains(req.owner_ref)) by {
                                        if obj.metadata.owner_references_contains(req.owner_ref) {
                                            assert(req.owner_ref != vd.controller_owner_ref());
                                            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                        }
                                    }
                                }
                            },
                            _ => {},
                        }
                    }
                },
                _ => {},
            }
        }
    }
    // we may lift the equivalence between owner_references_contains and owner_references->0.filter(...) == [...] to a lemma
    let controller_ref_singleton_seq = seq![vd.controller_owner_ref()];
    assert(controller_ref_singleton_seq.contains(vd.controller_owner_ref())) by {
        assert(controller_ref_singleton_seq[0] == vd.controller_owner_ref());
    }
    assert forall |k: ObjectRef| { // <==
        let obj = s_prime.resources()[k];
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& VReplicaSetView::unmarshal(obj) is Ok
        &&& obj.metadata.namespace == vd.metadata.namespace
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == controller_ref_singleton_seq
    } implies {
        &&& s.resources().contains_key(k)
        // TODO: weaken to allow status update requests
        &&& s.resources()[k] == s_prime.resources()[k]
    } by {
        let obj = s_prime.resources()[k];
        // <==
        if msg.content.is_APIRequest() && msg.dst.is_APIServer() {
            // must be a create request
            match msg.content.get_APIRequest_0() {
                APIRequest::CreateRequest(req) => {
                    // create can only add new object
                    if !s.resources().contains_key(k) {
                        assert(helper_invariants::no_other_pending_create_request_interferes_with_vd_reconcile(req, vd)(s));
                        // req succeed
                        let resp = handle_create_request(cluster.installed_types, req, s.api_server).1;
                        if resp.res is Ok {
                            let created_obj = resp.res->Ok_0;
                            assert(s_prime.resources() == s.resources().insert(created_obj.object_ref(), created_obj));
                            assert((k, obj) == (created_obj.object_ref(), created_obj));
                            // trigger no_other_pending_create_request_interferes_with_vd_reconcile
                            assert(created_obj.metadata.owner_references_contains(vd.controller_owner_ref())) by {
                                seq_filter_is_a_subset_of_original_seq(created_obj.metadata.owner_references->0, controller_owner_filter());
                            }
                        } else {
                            assert(s.resources() == s_prime.resources());
                        }
                    }
                },
                APIRequest::GetThenUpdateRequest(req) => {
                    assert(helper_invariants::no_other_pending_get_then_update_request_interferes_with_vd_reconcile(req, vd)(s));
                    // fields we care about are not altered
                    if s.resources().contains_key(k) {
                        if req.key() == k {
                            // either obj in s has the right controller owner ref, or it's updated
                            // both cases are excluded by no_other_pending_get_then_update_request_interferes_with_vd_reconcile
                            let old_obj = s.resources()[k];
                            if old_obj.metadata.owner_references_contains(vd.controller_owner_ref()) {
                                assert(!old_obj.metadata.owner_references_contains(req.owner_ref)) by {
                                    if old_obj.metadata.owner_references_contains(req.owner_ref) {
                                        // ruled out by no_other_pending_get_then_update_request_interferes_with_vd_reconcile
                                        assert(req.owner_ref != vd.controller_owner_ref()) by {
                                            if req.owner_ref == vd.controller_owner_ref() {
                                                assert(req.key().namespace == vd.metadata.namespace->0);
                                                assert(false);
                                            }
                                        }
                                        // each_object_in_etcd_has_at_most_one_controller_owner
                                        assert(old_obj.metadata.owner_references->0.filter(controller_owner_filter()) == controller_ref_singleton_seq) by {
                                            assert(old_obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
                                        }
                                        assert(old_obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                        assert(false);
                                    }
                                }
                            } else {
                                if old_obj.metadata.owner_references_contains(req.owner_ref) {
                                    // update fails
                                    if obj.metadata.owner_references != req.obj.metadata.owner_references {
                                        assert(s.resources()[k] == s_prime.resources()[k]);
                                    } else {
                                        assert(obj.metadata.owner_references_contains(vd.controller_owner_ref())) by {
                                            seq_filter_is_a_subset_of_original_seq(obj.metadata.owner_references->0, controller_owner_filter());
                                        }
                                        assert(false);
                                    }
                                } else {
                                    // update fails
                                    assert(s.resources()[k] == s_prime.resources()[k]);
                                }
                            }
                        }
                    }
                },
                APIRequest::UpdateRequest(req) => {
                    assert(helper_invariants::no_other_pending_update_request_interferes_with_vd_reconcile(req, vd)(s));
                    if s.resources().contains_key(k) {
                        let (s_prime_server, resp) = handle_update_request(cluster.installed_types, req, s.api_server);
                        let old_obj = s.resources()[k];
                        if req.key() == k && resp.res is Ok {
                            if old_obj.metadata.owner_references is Some
                                && old_obj.metadata.owner_references_contains(vd.controller_owner_ref()) {
                                assert(false); // impossible by no_other_pending_update_request_interferes_with_vd_reconcile
                            } else {
                                if req.obj.metadata.owner_references is Some
                                    && req.obj.metadata.owner_references->0.contains(vd.controller_owner_ref()) {
                                    assert(false); // impossible by no_other_pending_update_request_interferes_with_vd_reconcile
                                } else {
                                    assert(obj.metadata.owner_references == req.obj.metadata.owner_references);
                                    seq_filter_contains_implies_seq_contains(obj.metadata.owner_references->0, controller_owner_filter(), vd.controller_owner_ref());
                                    assert(false);
                                }
                            }   
                        } else {
                            assert(s.resources()[k] == s_prime.resources()[k]);
                        }
                    }
                },
                _ => {}
            }
        }
    }
}

// Havoc function for VDeploymentView.
uninterp spec fn make_vd() -> VDeploymentView;

}