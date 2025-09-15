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
    proof::{predicate::*, helper_invariants},
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use vstd::{seq_lib::*, prelude::*, map_lib::*};
use crate::vstd_ext::{seq_lib::*, set_lib::*};

verus! {

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
ensures
    resp_msg == handle_list_request_msg(req_msg, s.api_server).1,
    resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s_prime),
{
    broadcast use group_seq_properties;
    VReplicaSetView::marshal_preserves_integrity();
    let vd = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    let req = req_msg.content.get_list_request();
    let list_req_filter = |o: DynamicObjectView| {
        // why changing the order of fields makes a difference
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
    }; 
    let resp_msg = handle_list_request_msg(req_msg, s.api_server).1;
    assert(resp_msg_is_ok_list_resp_containing_matched_vrs(vd, controller_id, resp_msg, s_prime)) by {
        assert(vd.metadata.namespace is Some);
        assert(req.kind == VReplicaSetView::kind());
        assert(req.namespace == vd.metadata.namespace->0);
        assert(resp_msg.content.is_list_response());
        assert(resp_msg.content.get_list_response() == handle_list_request(req, s.api_server));
        assert(resp_msg.content.get_list_response().res is Ok);
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
            assert(list_req_filter(o));
            assert(s.resources().contains_key(o.object_ref()));
            assert(s.resources()[o.object_ref()] == o);
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
            assert(resp_objs[i].metadata == vrs.metadata);
            // assert(resp_objs[i].object_ref() == key);
            assert(valid_owned_vrs(vrs, vd));
            assert(vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]) by {
                // each_object_in_etcd_has_at_most_one_controller_owner
                assert(vrs.metadata.owner_references->0.filter(controller_owner_filter()).contains(vd.controller_owner_ref()));
            }
        }
        // TODO: add DS lemma to prove it
        assume(managed_vrs_list.map_values((|vrs: VReplicaSetView| vrs.object_ref())).to_set() == filter_obj_keys_managed_by_vd(vd, s_prime));
    }
    return resp_msg;
}

// staged, we need to handle collision
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
    local_state_is(vd, controller_id, None, n)(s),
ensures
    res.0 == handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1,
    resp_msg_matches_req_msg(res.0, req_msg),
    resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, res.0, res.1)(s_prime),
    etcd_state_is(vd, controller_id, Some(((res.1).0, (res.1).1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime),
    local_state_is(vd, controller_id, None, n)(s_prime),
{
    broadcast use group_seq_properties;
    VReplicaSetView::marshal_preserves_integrity();
    let vd = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    let request = req_msg.content.get_APIRequest_0().get_CreateRequest_0();
    let new_vrs = make_replica_set(vd);
    assert(request == CreateRequest {
        namespace: vd.metadata.namespace.unwrap(),
        obj: new_vrs.marshal()
    });
    assert(s_prime.api_server == handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).0);
    assert(create_request_admission_check(cluster.installed_types, request, s.api_server) is None);
    let resp_msg = handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1;
    let resp_obj = resp_msg.content.get_create_response().res.unwrap();
    let key = resp_obj.object_ref();
    assert(s_prime.resources() == s.resources().insert(key, resp_obj)) by {
        assume(!s.resources().contains_key(key)); // generate_name is unique
        assert(request.obj.metadata.owner_references is Some);
        assert(resp_obj.metadata.owner_references is Some);
        assert(request.obj.metadata.owner_references->0.len() == 1);
        assert(request.obj.metadata.owner_references->0 == resp_obj.metadata.owner_references->0);
        assert(created_object_validity_check(resp_obj, cluster.installed_types) is None);
    }
    assert(VReplicaSetView::unmarshal(resp_obj) is Ok);
    let vrs = VReplicaSetView::unmarshal(resp_obj)->Ok_0;
    let etcd_obj = s_prime.resources()[key];
    let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
    assert(vrs.metadata.uid is Some);
    assert(resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, resp_msg, (etcd_obj.metadata.uid->0, key))(s_prime)) by {
        assert(vrs.object_ref() == key);
        assert(vrs.metadata.owner_references is Some);
        assert(vrs.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]);
        assert(vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1));
        assert(s_prime.resources().contains_key(key));
        assert(valid_owned_obj_key(vd, s_prime)(key));
        assert(filter_new_vrs_keys(vd.spec.template, s_prime)(key));
        assert(vrs_weakly_eq(etcd_vrs, vrs));
        assert(etcd_vrs.spec == vrs.spec);
    }
    return (resp_msg, (etcd_obj.metadata.uid->0, key));
}

pub proof fn lemma_scale_scale_new_vrs_req_returns_ok(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    req_msg: Message, nv_uid_key_replicas: (Uid, ObjectRef, int), n: nat
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_pending_scale_new_vrs_req_in_flight(vd, controller_id, req_msg, (nv_uid_key_replicas.0, nv_uid_key_replicas.1))(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, Some(nv_uid_key_replicas), n)(s),
    // TODO: isolate local_state_is
    // local_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n)(s),
    nv_uid_key_replicas.2 != vd.spec.replicas.unwrap_or(int1!()),
ensures
    resp_msg == handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1,
    resp_msg_is_ok_scale_new_vrs_resp_in_flight(vd, controller_id, resp_msg, (nv_uid_key_replicas.0, nv_uid_key_replicas.1))(s_prime),
    etcd_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime),
    // local_state_is(vd, controller_id, Some((nv_uid_key_replicas.0, nv_uid_key_replicas.1, vd.spec.replicas.unwrap_or(int1!()))), n)(s_prime),
{
    let vd = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    let req = req_msg.content.get_get_then_update_request();
    let etcd_obj = s.resources()[req.key()];
    // update can succeed
    assert(etcd_obj.metadata.owner_references_contains(req.owner_ref));
    assert(req.owner_ref == vd.controller_owner_ref());
    assert(s.resources().contains_key(req.key()));
    assert(s_prime.api_server == handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).0);

    let resp_msg = handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1;
    assert(resp_msg_is_ok_scale_new_vrs_resp_in_flight(vd, controller_id, resp_msg, (nv_uid_key_replicas.0, nv_uid_key_replicas.1))(s_prime)) by {
        assert(Cluster::has_pending_k8s_api_req_msg(controller_id, s_prime, vd.object_ref()));
        assert(req_msg.src == HostId::Controller(controller_id, vd.object_ref()));
        assert(req_msg.dst == HostId::APIServer);
        assert(req_msg.content.is_APIRequest());
        assert(req_msg.content.get_APIRequest_0().is_GetThenUpdateRequest());
        assert(s_prime.in_flight().contains(resp_msg));
        assert(resp_msg_matches_req_msg(resp_msg, req_msg));
        assert(resp_msg.content.get_get_then_update_response().res is Ok);
    }



    return resp_msg;
}

#[verifier(external_body)]
pub proof fn lemma_get_then_update_request_returns_ok_after_scale_down_old_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    req_msg: Message, nv_uid_key: (Uid, ObjectRef), n: nat
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_pending_scale_old_vrs_req_in_flight(vd, controller_id, req_msg, nv_uid_key.0)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), n)(s),
    local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), (n - nat1!()) as nat)(s),
ensures
    resp_msg == handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1,
    resp_msg_is_ok_scale_old_vrs_resp_in_flight(vd, controller_id, resp_msg, nv_uid_key.0)(s_prime),
    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), (n - nat1!()) as nat)(s_prime),
    local_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(int1!()))), (n - nat1!()) as nat)(s_prime),
{
    return handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1;
}

#[verifier(external_body)]
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
    (!Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg)
        || !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())),
ensures
    etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)(s) ==> etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)(s_prime),
{}

pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int,// new_vrs, old_vrs_list
    msg: Message, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    forall |vd| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(cluster, controller_id)(s),
    (!Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg)
        || !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())),
ensures
    local_state_is(vd, controller_id, nv_uid_key_replicas, n)(s) ==> local_state_is(vd, controller_id, nv_uid_key_replicas, n)(s_prime),
{
    broadcast use group_seq_properties;
    let list_req_filter = |o: DynamicObjectView| {
        &&& o.object_ref().namespace == vd.metadata.namespace->0
        &&& o.object_ref().kind == VReplicaSetView::kind()
    }; 
    let objs = s.resources().values().filter(list_req_filter).to_seq();
    let filtered_vrs_list = objects_to_vrs_list(objs).unwrap().filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd));
    let objs_prime = s_prime.resources().values().filter(list_req_filter).to_seq();
    let filtered_vrs_list_prime = objects_to_vrs_list(objs_prime).unwrap().filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd));
    assert forall |vrs| filtered_vrs_list.contains(vrs) implies filtered_vrs_list_prime.contains(vrs) by {
        assume({
            let etcd_obj = s.resources()[vrs.object_ref()];
            &&& s.resources().contains_key(vrs.object_ref())
            &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
            &&& etcd_obj.metadata.namespace == vd.metadata.namespace
            &&& etcd_obj.metadata.owner_references is Some
            &&& etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
        });
        lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
            s, s_prime, vd, cluster, controller_id, vrs.object_ref(), msg
        );
        assume(filtered_vrs_list_prime.contains(vrs));
    }
    assert forall |vrs| filtered_vrs_list_prime.contains(vrs) implies filtered_vrs_list.contains(vrs) by {
        if !filtered_vrs_list.contains(vrs) {
            if msg.content.is_APIRequest() && msg.dst.is_APIServer() {
                match msg.src {
                    HostId::Controller(id, cr_key) => {
                        assume(false);
                    },
                    _ => {
                        assume(false);
                    },
                }
            }
        }
    }
    // second, prove local_state_is_valid_and_coherent(vd, controller_id)(s_prime)
    assume(false);
}

// filter_obj_keys_managed_by_vd is maintained
#[verifier(external_body)]
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_objects_owned_by_vd(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int,
    msg: Message
)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    forall |vd| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(cluster, controller_id)(s),
    // equal to msg.src != HostId::Controller(controller_id, vd.object_ref())
    (!Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg)
        || !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())),
ensures
    ({
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr)->Ok_0;
        &&& filter_obj_keys_managed_by_vd(triggering_cr, s) == filter_obj_keys_managed_by_vd(triggering_cr, s_prime)
    }),
{}

// This lemma proves for all objects owned by vd (checked by namespace and owner_ref),
// the API request msg does not change or delete the object
// as the direct result of rely condition and non-interference property.
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_object_owned_by_vd(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int,
    key: ObjectRef, msg: Message
)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    forall |vd| helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s),
    vd_rely_condition(cluster, controller_id)(s),
    // object in etcd is owned by vd
    ({
        let etcd_obj = s.resources()[key];
        &&& s.resources().contains_key(key)
        &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
        &&& etcd_obj.metadata.namespace == vd.metadata.namespace
        &&& etcd_obj.metadata.owner_references is Some
        &&& etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]
    }),
    // equal to msg.src != HostId::Controller(controller_id, vd.object_ref())
    (!Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg)
        || !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())),
ensures
    ({
        let etcd_obj = s.resources()[key];
        &&& s_prime.resources().contains_key(key)
        &&& etcd_obj == s_prime.resources()[key]
    }),
{
    assert(s.resources().contains_key(key));
    let etcd_obj = s.resources()[key];
    assert(VReplicaSetView::unmarshal(etcd_obj) is Ok);
    VReplicaSetView::marshal_preserves_integrity();
    // trigger rely condition,
    // rule out cases when etcd_obj get deleted with rely_delete and handle_delete_eq checks
    assert(etcd_obj.metadata.owner_references->0.contains(vd.controller_owner_ref())) by {
        broadcast use group_seq_properties;
        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vd.controller_owner_ref()]);
        seq_filter_contains_implies_seq_contains(etcd_obj.metadata.owner_references->0, controller_owner_filter(), vd.controller_owner_ref());
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
                                assert(!etcd_obj.metadata.owner_references_contains(req.owner_ref)) by {
                                    if etcd_obj.metadata.owner_references_contains(req.owner_ref) {
                                        assert(req.owner_ref != vd.controller_owner_ref());
                                        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
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
                                assert(!etcd_obj.metadata.owner_references_contains(req.owner_ref)) by {
                                    if etcd_obj.metadata.owner_references_contains(req.owner_ref) {
                                        assert(req.owner_ref != vd.controller_owner_ref());
                                        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
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
                                assert(!etcd_obj.metadata.owner_references_contains(req.owner_ref)) by {
                                    if etcd_obj.metadata.owner_references_contains(req.owner_ref) {
                                        assert(req.owner_ref != vd.controller_owner_ref());
                                        assert(etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
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

// Havoc function for VDeploymentView.
uninterp spec fn make_vd() -> VDeploymentView;

}