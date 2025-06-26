// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_invariants, helper_lemmas, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*};
use vstd::{map::*, map_lib::*, prelude::*};

verus! {

pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
    s: ClusterState, s_prime: ClusterState, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, 
    msg: Message,
)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s),
        Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
        helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s),
        (!Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
            || !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())),
    ensures
        matching_pods(vrs, s.resources()) == matching_pods(vrs, s_prime.resources()),
{
    if msg.content.is_get_then_delete_request() {
        let req = msg.content.get_get_then_delete_request();
        if req.key.kind == Kind::PodKind
            && req.key.namespace == vrs.metadata.namespace.unwrap()
            && s.resources().contains_key(req.key) {
            let obj = s.resources()[req.key];
            if obj.metadata.owner_references_contains(req.owner_ref) {
                let owners = obj.metadata.owner_references.get_Some_0();
                let controller_owners = owners.filter(
                    |o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0()
                );
                assert(req.owner_ref.controller.is_Some() && req.owner_ref.controller.get_Some_0());
                assert(controller_owners.contains(req.owner_ref));
                assert(!controller_owners.contains(vrs.controller_owner_ref()));
            }
        }
    } else if msg.content.is_get_then_update_request() { 
        let req = msg.content.get_get_then_update_request();
        if req.obj.kind == Kind::PodKind 
            && req.key().namespace == vrs.metadata.namespace.unwrap()
            && s.resources().contains_key(req.key()) {
            let obj = s.resources()[req.key()];
            if obj.metadata.owner_references_contains(req.owner_ref) {
                let owners = obj.metadata.owner_references.get_Some_0();
                let controller_owners = owners.filter(
                    |o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0()
                );
                assert(req.owner_ref.controller.is_Some() && req.owner_ref.controller.get_Some_0());
                assert(controller_owners.contains(req.owner_ref));
                assert(!controller_owners.contains(vrs.controller_owner_ref()));
            }
        }
    }
    assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
    helper_lemmas::matching_pods_equal_to_matching_pod_entries_values(vrs, s.resources());
    helper_lemmas::matching_pods_equal_to_matching_pod_entries_values(vrs, s_prime.resources());
}

pub proof fn lemma_list_pods_request_returns_ok_list_resp_containing_matching_pods(
    s: ClusterState, s_prime: ClusterState, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, 
    msg: Message,
) -> (resp_msg: Message)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        req_msg_is_list_pods_req(vrs, msg),
        Cluster::desired_state_is(vrs)(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::etcd_is_finite()(s),
    ensures
        resp_msg == handle_list_request_msg(msg, s.api_server).1,
        resp_msg_is_ok_list_resp_containing_matching_pods(s_prime, vrs, resp_msg),
{
    let pre = {
        &&& cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg)))
        &&& req_msg_is_list_pods_req(vrs, msg)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::etcd_is_finite()(s)
    };

    let resp_msg = handle_list_request_msg(msg, s.api_server).1;
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let resp_obj_keys = resp_objs.map_values((|obj: DynamicObjectView| obj.object_ref()));

    assert forall |o: DynamicObjectView| #![auto]
    pre && matching_pods(vrs, s_prime.resources()).contains(o)
    implies resp_objs.to_set().contains(o) by {
        // Tricky reasoning about .to_seq
        let selector = |o: DynamicObjectView| {
            &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
            &&& o.object_ref().kind == PodView::kind()
        };
        let selected_elements = s.resources().values().filter(selector);
        assert(selected_elements.contains(o));
        lemma_values_finite(s.resources());
        finite_set_to_seq_contains_all_set_elements(selected_elements);
    }

    assert forall |o: DynamicObjectView| #![auto]
    pre && resp_objs.contains(o)
    implies !PodView::unmarshal(o).is_err()
            && o.metadata.namespace == vrs.metadata.namespace by {
        // Tricky reasoning about .to_seq
        let selector = |o: DynamicObjectView| {
            &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
            &&& o.object_ref().kind == PodView::kind()
        };
        let selected_elements = s.resources().values().filter(selector);
        lemma_values_finite(s.resources());
        finite_set_to_seq_contains_all_set_elements(selected_elements);
        assert(resp_objs == selected_elements.to_seq());
        assert(selected_elements.contains(o));
    }
    seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(resp_objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err());

    // TODO: Shorten up this proof.
    assert_by(objects_to_pods(resp_objs).unwrap().no_duplicates(), {
        let selector = |o: DynamicObjectView| {
            &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
            &&& o.object_ref().kind == PodView::kind()
        };
        let selected_elements = s.resources().values().filter(selector);
        lemma_values_finite(s.resources());
        finite_set_to_seq_has_no_duplicates(selected_elements);
        let selected_elements_seq = selected_elements.to_seq();
        let pods_seq = objects_to_pods(selected_elements_seq).unwrap();
        assert(selected_elements_seq.no_duplicates());

        assert forall |x: DynamicObjectView, y: DynamicObjectView| #![auto]
            x != y
            && selected_elements_seq.contains(x)
            && selected_elements_seq.contains(y) implies x.object_ref() != y.object_ref() by {
            finite_set_to_seq_contains_all_set_elements(selected_elements);
            assert(selected_elements.contains(x));
            assert(selected_elements.contains(y));
        }

        let lem = forall |x: DynamicObjectView, y: DynamicObjectView| #![auto]
            x != y
            && selected_elements_seq.contains(x)
            && selected_elements_seq.contains(y) ==> x.object_ref() != y.object_ref();

        assert forall |i: int, j: int| #![auto]
            0 <= i && i < pods_seq.len() && (0 <= j && j < pods_seq.len()) && !(i == j)
            && objects_to_pods(selected_elements_seq).is_Some()
            && lem
            implies pods_seq[i] != pods_seq[j] by {
            let o1 = selected_elements_seq[i];
            let o2 = selected_elements_seq[j];
            assert(o1.object_ref() != o2.object_ref());
            PodView::marshal_preserves_integrity();
            seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(selected_elements_seq, |o: DynamicObjectView| PodView::unmarshal(o).is_err());
            assert(selected_elements_seq.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0);
            assert(selected_elements_seq.contains(o1));
            assert(selected_elements_seq.contains(o2));
        }

        assert(pods_seq.no_duplicates());
    });

    assert_by(resp_obj_keys.no_duplicates(), {
        let selector = |o: DynamicObjectView| {
            &&& o.object_ref().namespace == msg.content.get_list_request().namespace
            &&& o.object_ref().kind == msg.content.get_list_request().kind
        };
        let selected_elements = s.resources().values().filter(selector);
        lemma_values_finite(s.resources());
        finite_set_to_seq_has_no_duplicates(selected_elements);
        let selected_elements_seq = selected_elements.to_seq();
        assert(selected_elements_seq.no_duplicates());
        assert forall |o1: DynamicObjectView, o2: DynamicObjectView| #![auto]
            o1 != o2
            && selected_elements_seq.contains(o1)
            && selected_elements_seq.contains(o2)
            && pre
            implies o1.object_ref() != o2.object_ref() by {
            finite_set_to_seq_contains_all_set_elements(selected_elements);
            assert(selected_elements.contains(o1));
            assert(selected_elements.contains(o2));
            assert(s.resources().values().contains(o1));
            assert(s.resources().values().contains(o2));
            assert(o1.object_ref() != o2.object_ref());
        }
        let selected_element_keys = selected_elements_seq.map_values(|o: DynamicObjectView| o.object_ref());
        assert(selected_element_keys.no_duplicates());
        assert(resp_obj_keys =~= selected_element_keys);
    });

    assert(matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set() && resp_objs.no_duplicates()) by {
        // reveal API server spec
        let selector = |o: DynamicObjectView| {
            &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
            &&& o.object_ref().kind == PodView::kind()
        };
        assert(resp_objs == s.resources().values().filter(selector).to_seq());
        // consistency of no_duplicates
        lemma_values_finite(s.resources());
        finite_set_to_finite_filtered_set(s.resources().values(), selector);
        finite_set_to_seq_has_no_duplicates(s.resources().values().filter(selector));
        assert(resp_objs.no_duplicates());

        // reveal matching_pods logic
        let matched_pods = matching_pods(vrs, s.resources());
        assert(matched_pods =~= s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj))) by {
            assert forall |obj| s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj) implies matched_pods.contains(obj) by {
                assert(owned_selector_match_is(vrs, obj));
                assert(s.resources().contains_key(obj.object_ref()) && s.resources()[obj.object_ref()] == obj);
                assert(matched_pods.contains(obj));                                                
            }
            assert forall |obj| matched_pods.contains(obj) implies s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj) by {
                assert(s.resources().contains_key(obj.object_ref()));
                assert(owned_selector_match_is(vrs, obj));
            }
            // optional if antisymmetry_of_set_equality is imported
            assert(forall |obj| matched_pods.contains(obj) == s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj));
        }
        assert(s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)) == matching_pods(vrs, s.resources()));
        
        // get rid of DS conversion, basically babysitting Verus
        assert(resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set() =~= s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj))) by {
            assert(resp_objs == s.resources().values().filter(selector).to_seq());
            assert((|obj : DynamicObjectView| owned_selector_match_is(vrs, obj) && selector(obj)) =~= (|obj : DynamicObjectView| owned_selector_match_is(vrs, obj)));
            seq_filter_preserves_no_duplicates(resp_objs, |obj| owned_selector_match_is(vrs, obj));
            seq_filter_is_a_subset_of_original_seq(resp_objs, |obj| owned_selector_match_is(vrs, obj));
            finite_set_to_seq_contains_all_set_elements(s.resources().values().filter(selector));
            finite_set_to_seq_contains_all_set_elements(s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)));
            // Fix to get rid of flaky proof.
            assert forall |obj| #![trigger owned_selector_match_is(vrs, obj)]
                resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set().contains(obj)
                implies
                s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj) by {
                assert(resp_objs.contains(obj));
                assert(s.resources().values().filter(selector).to_seq().contains(obj));
                assert(s.resources().values().filter(selector).contains(obj));
                assert(s.resources().values().contains(obj));
                assert(owned_selector_match_is(vrs, obj));
                assert(s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj));
            }
            assert forall |obj| #![trigger owned_selector_match_is(vrs, obj)]
                s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj)
                implies
                resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set().contains(obj) by {
                assert(s.resources().values().contains(obj));
                assert(selector(obj));
                assert(s.resources().values().filter(selector).contains(obj));
                assert(s.resources().values().filter(selector).to_seq().contains(obj));
                assert(resp_objs.contains(obj));
                assert(resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj));
                assert(resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set().contains(obj));
            }
        }
    }

    return resp_msg;
}

pub proof fn lemma_create_matching_pod_request_adds_matching_pod_and_returns_ok(
    s: ClusterState, s_prime: ClusterState, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, 
    msg: Message,
) -> (resp_msg: Message)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        req_msg_is_create_matching_pod_req(vrs, msg),
        Cluster::desired_state_is(vrs)(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s),
        helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s),
        Cluster::etcd_is_finite()(s),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    ensures
        resp_msg == handle_create_request_msg(cluster.installed_types, msg, s.api_server).1,
        resp_msg.content.get_create_response().res.is_Ok(),
        matching_pods(vrs, s.resources()).insert(
            new_obj_in_etcd(
                s, cluster, 
                CreateRequest {
                    namespace: vrs.metadata.namespace.unwrap(),
                    obj: make_pod(vrs).marshal(),
                }
            )
        ) == matching_pods(vrs, s_prime.resources()),
        matching_pods(vrs, s.resources()).len() + 1 == matching_pods(vrs, s_prime.resources()).len(),
{
    let created_obj = new_obj_in_etcd(s, cluster, msg.content.get_create_request());

    PodView::marshal_preserves_integrity();
    generated_name_is_unique(s.api_server);

    // reasoning about owner_references to prove that 
    // our request creates a vrs-owned pod.
    assert(created_obj.metadata.owner_references == Some(seq![vrs.controller_owner_ref()]));
    assert(created_obj.metadata.owner_references.get_Some_0()[0] == vrs.controller_owner_ref());
    assert(created_obj.metadata.owner_references_contains(vrs.controller_owner_ref()));
    
    assert(owned_selector_match_is(vrs, created_obj));

    assert(
        matching_pod_entries(vrs, s_prime.resources())
        == matching_pod_entries(vrs, s.resources()).insert(created_obj.object_ref(), created_obj)
    );
    assert_by(
        matching_pod_entries(vrs, s.resources()).insert(created_obj.object_ref(), created_obj).values()
        =~= matching_pod_entries(vrs, s.resources()).values().insert(created_obj),
        {
            assert forall |o: DynamicObjectView|
                #[trigger] matching_pod_entries(vrs, s.resources()).values().insert(created_obj).contains(o) 
                implies matching_pod_entries(vrs, s.resources()).insert(created_obj.object_ref(), created_obj).values().contains(o) by {
                if o == created_obj {
                    assert(
                        matching_pod_entries(vrs, s.resources())
                            .insert(created_obj.object_ref(), created_obj)[created_obj.object_ref()] == created_obj
                    );
                } else {
                    assert(matching_pod_entries(vrs, s.resources()).values().contains(o));
                    let key = choose |key: ObjectRef|
                        matching_pod_entries(vrs, s.resources()).contains_key(key)
                        && #[trigger] matching_pod_entries(vrs, s.resources())[key] == o;
                    assert(
                        matching_pod_entries(vrs, s.resources())
                            .insert(created_obj.object_ref(), created_obj)[key] == o
                    );
                }
            }
        }
    );

    a_submap_of_a_finite_map_is_finite(
        matching_pod_entries(vrs, s.resources()),
        s.resources()
    );
    lemma_values_finite(matching_pod_entries(vrs, s.resources()));
    
    helper_lemmas::matching_pods_equal_to_matching_pod_entries_values(vrs, s.resources());
    helper_lemmas::matching_pods_equal_to_matching_pod_entries_values(vrs, s_prime.resources());
    return handle_create_request_msg(cluster.installed_types, msg, s.api_server).1;
}

pub proof fn lemma_get_then_delete_matching_pod_request_deletes_matching_pod_and_returns_ok(
    s: ClusterState, s_prime: ClusterState, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, 
    msg: Message,
) -> (resp_msg: Message)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        req_msg_is_get_then_delete_matching_pod_req(vrs, controller_id, msg)(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s),
        helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s),
        Cluster::etcd_is_finite()(s),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    ensures
        resp_msg == handle_get_then_delete_request_msg(msg, s.api_server).1,
        resp_msg.content.get_get_then_delete_response().res.is_Ok(),
        // identifies specific pod deleted.
        ({
            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
            let filtered_pods = state.filtered_pods.unwrap();
            let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
            let diff = state.reconcile_step.get_AfterDeletePod_0();
            matching_pods(vrs, s_prime.resources()) == matching_pods(vrs, s.resources()).remove(
                s.resources()[filtered_pod_keys[diff as int]]
            )
        }),
        // should be an obvious corollary of `generated_name_is_unique`.
        matching_pods(vrs, s.resources()).len() == matching_pods(vrs, s_prime.resources()).len() + 1,
{
    let key = msg.content.get_get_then_delete_request().key;
    let obj = s.resources()[key];

    assert(
        matching_pod_entries(vrs, s_prime.resources())
        == matching_pod_entries(vrs, s.resources()).remove(key)
    );
    assert(
        matching_pod_entries(vrs, s.resources()).remove(key).values()
        == matching_pod_entries(vrs, s.resources()).values().remove(obj)
    );

    a_submap_of_a_finite_map_is_finite(
        matching_pod_entries(vrs, s.resources()),
        s.resources()
    );
    lemma_values_finite(matching_pod_entries(vrs, s.resources()));

    helper_lemmas::matching_pods_equal_to_matching_pod_entries_values(vrs, s.resources());
    helper_lemmas::matching_pods_equal_to_matching_pod_entries_values(vrs, s_prime.resources());
    return handle_get_then_delete_request_msg(msg, s.api_server).1;
}

// OBSOLETE FUNCTIONS ------ Remove as others get used.

// TODO: broken by changed ESR spec, needs new set-based (rather than map-based) argument.
#[verifier(external_body)]
pub proof fn lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
    s: ClusterState, s_prime: ClusterState, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, 
    msg: Message,
)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s),
        forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s)),
        forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s)),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vrs_rely(other_id)(s)
    ensures
        matching_pods(vrs, s.resources()) == matching_pods(vrs, s_prime.resources()),
{
    if msg.src.is_Controller() {
        let id = msg.src.get_Controller_0();
        assert(
            (id != controller_id ==> cluster.controller_models.remove(controller_id).contains_key(id)));
        // Invoke non-interference lemma by trigger.
        assert(id != controller_id ==> vrs_rely(id)(s));
    }

    // Dispatch through all the requests which may mutate the k-v store.
    let mutates_key = if msg.content.is_create_request() {
        let req = msg.content.get_create_request();
        Some(ObjectRef{
            kind: req.obj.kind,
            name: if req.obj.metadata.name.is_Some() {
                req.obj.metadata.name.unwrap()
            } else {
                generate_name(s.api_server)
            },
            namespace: req.namespace,
        })
    } else if msg.content.is_delete_request() {
        let req = msg.content.get_delete_request();
        Some(req.key)
    } else if msg.content.is_update_request() {
        let req = msg.content.get_update_request();
        Some(req.key())
    } else if msg.content.is_update_status_request() {
        let req = msg.content.get_update_status_request();
        Some(req.key())
    } else {
        None
    };

    match mutates_key {
        Some(key) => {
            assert_maps_equal!(s.resources().remove(key) == s_prime.resources().remove(key));
            assert_maps_equal!(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
        },
        _ => {}
    };
}

// TODO: broken by changed ESR spec, needs new set-based (rather than map-based) argument.
#[verifier(external_body)]
pub proof fn lemma_api_request_not_made_by_vrs_maintains_matching_pods(
    s: ClusterState, s_prime: ClusterState, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
    diff: int, msg: Message, req_msg: Option<Message>
)
    requires
        req_msg.is_Some() ==> msg != req_msg.get_Some_0(),
        req_msg == s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg,
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s),
        helper_invariants::no_pending_interfering_update_request()(s),
        helper_invariants::no_pending_interfering_update_status_request()(s),
        helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s),
        helper_invariants::no_pending_mutation_request_not_from_controller_on_pods()(s),
        helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s),
        helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s),
        helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)(s),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vrs_rely(other_id)(s)
    ensures
        matching_pods(vrs, s.resources()) == matching_pods(vrs, s_prime.resources()),
{
    if msg.src.is_Controller() {
        let id = msg.src.get_Controller_0();
        assert(
            (id != controller_id ==> cluster.controller_models.remove(controller_id).contains_key(id)));
        // Invoke non-interference lemma by trigger.
        assert(id != controller_id ==> vrs_rely(id)(s));
    }

    // Dispatch through all the requests which may mutate the k-v store.
    let mutates_key = if msg.content.is_create_request() {
        let req = msg.content.get_create_request();
        Some(ObjectRef{
            kind: req.obj.kind,
            name: if req.obj.metadata.name.is_Some() {
                req.obj.metadata.name.unwrap()
            } else {
                generate_name(s.api_server)
            },
            namespace: req.namespace,
        })
    } else if msg.content.is_delete_request() {
        let req = msg.content.get_delete_request();
        Some(req.key)
    } else if msg.content.is_update_request() {
        let req = msg.content.get_update_request();
        Some(req.key())
    } else if msg.content.is_update_status_request() {
        let req = msg.content.get_update_status_request();
        Some(req.key())
    } else {
        None
    };

    match mutates_key {
        Some(key) => {
            assert_maps_equal!(s.resources().remove(key) == s_prime.resources().remove(key));
            assert_maps_equal!(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
        },
        _ => {}
    };
}

}
