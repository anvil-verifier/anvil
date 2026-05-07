// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::vstatefulset_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, label_selector::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    api_server::{types::APIServerStep, state_machine::*},
    builtin_controllers::types::BuiltinControllerChoice, cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::resource_builder::*;
use crate::rabbitmq_controller::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants, liveness::spec::assumption_and_invariants_of_all_phases, predicate::*,
        resource::*, helper_lemmas::*, guarantee::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*, rely_guarantee::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*, multiset::*};

verus! {

// Proves AtAfterKRequestStep(Get, sub_resource) ~> resource_state_matches(sub_resource, rabbitmq) and AtAfterKRequestStep(Get, sub_resource) ~>
// AtAfterKRequestStep(Get, next_resource). The second one is not applicable to StatefulSet which doesn't have a next resource.
//
// The proof contains two part: resource_key exists or does not exist at first. The proof of both parts contains several times of applying
// wf1, handle_get_request => continue_reconcile => handle_create/update_request => continue_reconcile.
pub proof fn lemma_from_after_get_resource_step_to_resource_matches(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, sub_resource: SubResource, next_resource: SubResource
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        sub_resource_needs_cm_rv(sub_resource) ==> // additionally requires cm_rv tracking
            spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id))
            .leads_to(lift_state(resource_state_matches(sub_resource, rabbitmq)))),
        next_resource_step_after(sub_resource) == after_get_k_request_step(next_resource) ==> spec.entails(
            lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id)))
        ),
        // Inductive form for every sub_resource. Stage 1 (SCM) and Stage 2 (others) in
        // lemma_true_leads_to_always_state_matches_for_all both consume this so they can run
        // leads_to_stable / leads_to_with_always against inductive_current_state_matches.
        // composition.rs in turn consumes the VStatefulSetView case to feed
        // lemma_inductive_current_state_matches_preserves_from_s_to_s_prime.
        spec.entails(
            lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id))
                .leads_to(lift_state(inductive_current_state_matches(rabbitmq, sub_resource, controller_id)))
        ),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let pre = pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id);

    // Split into: key exists or key doesn't exist
    let pre_with_key = |s: ClusterState| {
        &&& s.resources().contains_key(resource_key)
        &&& pre(s)
    };
    let pre_without_key = |s: ClusterState| {
        &&& !s.resources().contains_key(resource_key)
        &&& pre(s)
    };

    // Case 1: key doesn't exist
    // Step 1a: get req ~> not_found resp
    let not_found_resp = at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, rabbitmq, controller_id);
    // ∃ msg version: pre_without_key has a specific req_msg
    let pre_without_key_msg = |req_msg| {
        |s: ClusterState| {
            &&& !s.resources().contains_key(resource_key)
            &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
        }
    };
    assert(lift_state(pre_without_key) == tla_exists(|msg| lift_state(pre_without_key_msg(msg)))) by {
        assert forall |ex| #[trigger] lift_state(pre_without_key).satisfied_by(ex) implies
            tla_exists(|msg| lift_state(pre_without_key_msg(msg))).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
            assert((|msg| lift_state(pre_without_key_msg(msg)))(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(lift_state(pre_without_key), tla_exists(|msg| lift_state(pre_without_key_msg(msg))));
    }
    assert forall |req_msg| spec.entails(#[trigger] lift_state(pre_without_key_msg(req_msg)).leads_to(lift_state(not_found_resp))) by {
        lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(
            controller_id, cluster, spec, sub_resource, rabbitmq, req_msg
        );
    }
    leads_to_exists_intro(spec, |msg| lift_state(pre_without_key_msg(msg)), lift_state(not_found_resp));

    // Step 1b: not_found resp ~> create step
    let create_req = pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq, controller_id);
    let not_found_resp_msg = |resp_msg| lift_state(
        resp_msg_is_the_in_flight_not_found_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)
    );
    assert(lift_state(not_found_resp) == tla_exists(|msg| not_found_resp_msg(msg))) by {
        assert forall |ex| #[trigger] lift_state(not_found_resp).satisfied_by(ex) implies
            tla_exists(|msg| not_found_resp_msg(msg)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
            let resp_msg = choose |resp_msg| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg.content.get_get_response().res is Err
                &&& resp_msg.content.get_get_response().res->Err_0 is ObjectNotFound
            };
            assert((|msg| not_found_resp_msg(msg))(resp_msg).satisfied_by(ex));
        }
        temp_pred_equality(lift_state(not_found_resp), tla_exists(|msg| not_found_resp_msg(msg)));
    }
    assert forall |resp_msg| spec.entails(#[trigger] not_found_resp_msg(resp_msg).leads_to(lift_state(create_req))) by {
        lemma_from_after_get_resource_step_to_after_create_resource_step(
            controller_id, cluster, spec, sub_resource, rabbitmq, resp_msg
        );
    }
    leads_to_exists_intro(spec, |msg| not_found_resp_msg(msg), lift_state(create_req));

    // Step 1c: create step ~> resource matches
    let create_req_msg = |req_msg| lift_state(
        |s: ClusterState| {
            &&& !s.resources().contains_key(resource_key)
            &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
        }
    );
    assert(lift_state(create_req) == tla_exists(|msg| create_req_msg(msg))) by {
        assert forall |ex| #[trigger] lift_state(create_req).satisfied_by(ex) implies
            tla_exists(|msg| create_req_msg(msg)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
            assert((|msg| create_req_msg(msg))(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(lift_state(create_req), tla_exists(|msg| create_req_msg(msg)));
    }
    assert forall |req_msg| spec.entails(#[trigger] create_req_msg(req_msg).leads_to(lift_state(resource_state_matches(sub_resource, rabbitmq)))) by {
        lemma_resource_state_matches_at_after_create_resource_step(
            controller_id, cluster, spec, sub_resource, rabbitmq, req_msg
        );
        leads_to_weaken::<ClusterState>(spec,
            create_req_msg(req_msg),
            lift_state(resource_state_matches(sub_resource, rabbitmq))
                .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id))),
            create_req_msg(req_msg),
            lift_state(resource_state_matches(sub_resource, rabbitmq))
        );
    }
    leads_to_exists_intro(spec, |msg| create_req_msg(msg), lift_state(resource_state_matches(sub_resource, rabbitmq)));

    // Chain case 1: pre_without_key ~> not_found_resp ~> create_req ~> resource_matches
    leads_to_trans_n!(
        spec,
        lift_state(pre_without_key),
        lift_state(not_found_resp),
        lift_state(create_req),
        lift_state(resource_state_matches(sub_resource, rabbitmq))
    );

    // Case 2: key exists
    // Step 2a: get req ~> ok resp
    let ok_resp = at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id);
    let pre_with_key_msg = |req_msg| {
        |s: ClusterState| {
            &&& s.resources().contains_key(resource_key)
            &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
        }
    };
    assert(lift_state(pre_with_key) == tla_exists(|msg| lift_state(pre_with_key_msg(msg)))) by {
        assert forall |ex| #[trigger] lift_state(pre_with_key).satisfied_by(ex) implies
            tla_exists(|msg| lift_state(pre_with_key_msg(msg))).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
            assert((|msg| lift_state(pre_with_key_msg(msg)))(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(lift_state(pre_with_key), tla_exists(|msg| lift_state(pre_with_key_msg(msg))));
    }
    assert forall |req_msg| spec.entails(#[trigger] lift_state(pre_with_key_msg(req_msg)).leads_to(lift_state(ok_resp))) by {
        lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(
            controller_id, cluster, spec, sub_resource, rabbitmq, req_msg
        );
    }
    leads_to_exists_intro(spec, |msg| lift_state(pre_with_key_msg(msg)), lift_state(ok_resp));

    // Step 2b: ok resp ~> update step
    let update_req = pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq, controller_id);
    let ok_resp_msg = |resp_msg| lift_state(
        resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)
    );
    assert(lift_state(ok_resp) == tla_exists(|msg| ok_resp_msg(msg))) by {
        assert forall |ex| #[trigger] lift_state(ok_resp).satisfied_by(ex) implies
            tla_exists(|msg| ok_resp_msg(msg)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
            let key = get_request(sub_resource, rabbitmq).key;
            let resp_msg = choose |resp_msg: Message| {
                let obj = resp_msg.content.get_get_response().res->Ok_0;
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg.content.get_get_response().res is Ok
                &&& match sub_resource {
                    SubResource::ServerConfigMap | SubResource::PluginsConfigMap => obj == s.resources()[key],
                    _ => {
                        &&& obj.spec == s.resources()[key].spec
                        &&& obj.metadata.without_resource_version() == s.resources()[key].metadata.without_resource_version()
                    }
                }
                &&& match sub_resource {
                    SubResource::HeadlessService | SubResource::Service => ServiceView::unmarshal(obj) is Ok,
                    SubResource::ErlangCookieSecret | SubResource::DefaultUserSecret => SecretView::unmarshal(obj) is Ok,
                    SubResource::PluginsConfigMap | SubResource::ServerConfigMap => ConfigMapView::unmarshal(obj) is Ok,
                    SubResource::ServiceAccount => ServiceAccountView::unmarshal(obj) is Ok,
                    SubResource::Role => RoleView::unmarshal(obj) is Ok,
                    SubResource::RoleBinding => RoleBindingView::unmarshal(obj) is Ok,
                    SubResource::VStatefulSetView => VStatefulSetView::unmarshal(obj) is Ok,
                }
            };
            assert((|msg| ok_resp_msg(msg))(resp_msg).satisfied_by(ex));
        }
        temp_pred_equality(lift_state(ok_resp), tla_exists(|msg| ok_resp_msg(msg)));
    }
    assert forall |resp_msg| spec.entails(#[trigger] ok_resp_msg(resp_msg).leads_to(lift_state(update_req))) by {
        lemma_from_after_get_resource_step_to_after_update_resource_step(
            controller_id, cluster, spec, sub_resource, rabbitmq, resp_msg
        );
    }
    leads_to_exists_intro(spec, |msg| ok_resp_msg(msg), lift_state(update_req));

    // Step 2c: update step ~> resource matches
    let update_req_msg = |req_msg| lift_state(
        req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, req_msg)
    );
    assert(lift_state(update_req) == tla_exists(|msg| update_req_msg(msg))) by {
        assert forall |ex| #[trigger] lift_state(update_req).satisfied_by(ex) implies
            tla_exists(|msg| update_req_msg(msg)).satisfied_by(ex) by {
            let s = ex.head();
            let req_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
            assert((|msg| update_req_msg(msg))(req_msg).satisfied_by(ex));
        }
        temp_pred_equality(lift_state(update_req), tla_exists(|msg| update_req_msg(msg)));
    }
    assert forall |req_msg| spec.entails(#[trigger] update_req_msg(req_msg).leads_to(lift_state(resource_state_matches(sub_resource, rabbitmq)))) by {
        lemma_resource_state_matches_at_after_update_resource_step(
            controller_id, cluster, spec, sub_resource, rabbitmq, req_msg
        );
        leads_to_weaken::<ClusterState>(spec,
            update_req_msg(req_msg),
            lift_state(resource_state_matches(sub_resource, rabbitmq))
                .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id))),
            update_req_msg(req_msg),
            lift_state(resource_state_matches(sub_resource, rabbitmq))
        );
    }
    leads_to_exists_intro(spec, |msg| update_req_msg(msg), lift_state(resource_state_matches(sub_resource, rabbitmq)));

    // Chain case 2: pre_with_key ~> ok_resp ~> update_req ~> resource_matches
    leads_to_trans_n!(
        spec,
        lift_state(pre_with_key),
        lift_state(ok_resp),
        lift_state(update_req),
        lift_state(resource_state_matches(sub_resource, rabbitmq))
    );

    // Combine case 1 and case 2: pre = pre_with_key \/ pre_without_key
    or_leads_to_combine(spec, lift_state(pre_with_key), lift_state(pre_without_key), lift_state(resource_state_matches(sub_resource, rabbitmq)));
    temp_pred_equality(lift_state(pre_with_key).or(lift_state(pre_without_key)), lift_state(pre));

    // Second ensures: pre ~> pending_req_in_flight_at_after_get_resource_step(next_resource)
    // We chain through the create/update ok responses to get to the next resource's get step.
    // Since the transition lemmas now bundle csm in pre/post, we thread csm from the create/update
    // step onward and weaken at the end to recover the second ensures.
    if next_resource_step_after(sub_resource) == after_get_k_request_step(next_resource) {
        let next_get = pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id);
        // csm-bundled aliases used for threading.
        let csm_and_next_get = |s: ClusterState| {
            &&& resource_state_matches(sub_resource, rabbitmq)(s)
            &&& pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id)(s)
        };

        // Case 1 (key doesn't exist): create path
        // Step 1c': create_req ~> csm /\ at_after_create_step_ok_resp (keep csm)
        let create_ok_resp = at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id);
        let csm_and_create_ok_resp = |s: ClusterState| {
            &&& resource_state_matches(sub_resource, rabbitmq)(s)
            &&& create_ok_resp(s)
        };
        assert forall |req_msg| spec.entails(#[trigger] create_req_msg(req_msg).leads_to(lift_state(csm_and_create_ok_resp))) by {
            lemma_resource_state_matches_at_after_create_resource_step(
                controller_id, cluster, spec, sub_resource, rabbitmq, req_msg
            );
            leads_to_weaken::<ClusterState>(spec,
                create_req_msg(req_msg),
                lift_state(resource_state_matches(sub_resource, rabbitmq))
                    .and(lift_state(create_ok_resp)),
                create_req_msg(req_msg),
                lift_state(csm_and_create_ok_resp)
            );
        }
        leads_to_exists_intro(spec, |msg| create_req_msg(msg), lift_state(csm_and_create_ok_resp));

        // Step 1d: csm /\ create_ok_resp ~> csm /\ next_get
        let csm_and_create_ok_resp_msg = |resp_msg| lift_state(|s: ClusterState|{
            &&& resource_state_matches(sub_resource, rabbitmq)(s)
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s)
        });
        assert(lift_state(csm_and_create_ok_resp) == tla_exists(|msg| csm_and_create_ok_resp_msg(msg))) by {
            assert forall |ex| #[trigger] lift_state(csm_and_create_ok_resp).satisfied_by(ex) implies
                tla_exists(|msg| csm_and_create_ok_resp_msg(msg)).satisfied_by(ex) by {
                let s = ex.head();
                let req_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
                let local_state = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state;
                let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
                let key = get_request(sub_resource, rabbitmq).key;
                let resp_msg = choose |resp_msg: Message| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    &&& resp_msg.content.get_create_response().res is Ok
                    &&& state_after_create(sub_resource, rabbitmq, resp_msg.content.get_create_response().res->Ok_0, unmarshalled_state) is Ok
                    &&& sub_resource == SubResource::ServerConfigMap ==>
                        s.resources().contains_key(key) && resp_msg.content.get_create_response().res->Ok_0 == s.resources()[key]
                };
                assert((|msg| csm_and_create_ok_resp_msg(msg))(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(csm_and_create_ok_resp), tla_exists(|msg| csm_and_create_ok_resp_msg(msg)));
        }
        assert forall |resp_msg| spec.entails(#[trigger] csm_and_create_ok_resp_msg(resp_msg).leads_to(lift_state(csm_and_next_get))) by {
            lemma_from_after_create_resource_step_to_after_get_next_resource_step(
                controller_id, cluster, spec, sub_resource, next_resource, rabbitmq, resp_msg
            );
        }
        leads_to_exists_intro(spec, |msg| csm_and_create_ok_resp_msg(msg), lift_state(csm_and_next_get));

        // Chain case 1: pre_without_key ~> not_found_resp ~> create_req ~> csm /\ create_ok_resp ~> csm /\ next_get
        leads_to_trans_n!(
            spec,
            lift_state(pre_without_key),
            lift_state(not_found_resp),
            lift_state(create_req),
            lift_state(csm_and_create_ok_resp),
            lift_state(csm_and_next_get)
        );

        // Case 2 (key exists): update path
        // Step 2c': update_req ~> csm /\ at_after_update_step_ok_resp (keep csm)
        let update_ok_resp = at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id);
        let csm_and_update_ok_resp = |s: ClusterState| {
            &&& resource_state_matches(sub_resource, rabbitmq)(s)
            &&& update_ok_resp(s)
        };
        assert forall |req_msg| spec.entails(#[trigger] update_req_msg(req_msg).leads_to(lift_state(csm_and_update_ok_resp))) by {
            lemma_resource_state_matches_at_after_update_resource_step(
                controller_id, cluster, spec, sub_resource, rabbitmq, req_msg
            );
            leads_to_weaken::<ClusterState>(spec,
                update_req_msg(req_msg),
                lift_state(resource_state_matches(sub_resource, rabbitmq))
                    .and(lift_state(update_ok_resp)),
                update_req_msg(req_msg),
                lift_state(csm_and_update_ok_resp)
            );
        }
        leads_to_exists_intro(spec, |msg| update_req_msg(msg), lift_state(csm_and_update_ok_resp));

        // Step 2d: csm /\ update_ok_resp ~> csm /\ next_get
        let csm_and_update_ok_resp_msg = |resp_msg| lift_state(|s: ClusterState|{
            &&& resource_state_matches(sub_resource, rabbitmq)(s)
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s)
        });
        assert(lift_state(csm_and_update_ok_resp) == tla_exists(|msg| csm_and_update_ok_resp_msg(msg))) by {
            assert forall |ex| #[trigger] lift_state(csm_and_update_ok_resp).satisfied_by(ex) implies
                tla_exists(|msg| csm_and_update_ok_resp_msg(msg)).satisfied_by(ex) by {
                let s = ex.head();
                let req_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
                let local_state = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state;
                let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
                let key = get_request(sub_resource, rabbitmq).key;
                let resp_msg = choose |resp_msg: Message| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    &&& resp_msg.content.get_get_then_update_response().res is Ok
                    &&& state_after_update(sub_resource, rabbitmq, resp_msg.content.get_get_then_update_response().res->Ok_0, unmarshalled_state) is Ok
                    &&& sub_resource == SubResource::ServerConfigMap ==>
                        s.resources().contains_key(key) && resp_msg.content.get_get_then_update_response().res->Ok_0 == s.resources()[key]
                };
                assert((|msg| csm_and_update_ok_resp_msg(msg))(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(csm_and_update_ok_resp), tla_exists(|msg| csm_and_update_ok_resp_msg(msg)));
        }
        assert forall |resp_msg| spec.entails(#[trigger] csm_and_update_ok_resp_msg(resp_msg).leads_to(lift_state(csm_and_next_get))) by {
            lemma_from_after_update_resource_step_to_after_get_next_resource_step(
                controller_id, cluster, spec, sub_resource, next_resource, rabbitmq, resp_msg
            );
        }
        leads_to_exists_intro(spec, |msg| csm_and_update_ok_resp_msg(msg), lift_state(csm_and_next_get));

        // Chain case 2: pre_with_key ~> ok_resp ~> update_req ~> csm /\ update_ok_resp ~> csm /\ next_get
        leads_to_trans_n!(
            spec,
            lift_state(pre_with_key),
            lift_state(ok_resp),
            lift_state(update_req),
            lift_state(csm_and_update_ok_resp),
            lift_state(csm_and_next_get)
        );

        // Combine case 1 and case 2 at csm_and_next_get, then weaken to next_get for the
        // existing second ensures (which doesn't track csm).
        or_leads_to_combine(spec, lift_state(pre_with_key), lift_state(pre_without_key), lift_state(csm_and_next_get));
        temp_pred_equality(lift_state(pre_with_key).or(lift_state(pre_without_key)), lift_state(pre));
        leads_to_weaken::<ClusterState>(spec, lift_state(pre), lift_state(csm_and_next_get), lift_state(pre), lift_state(next_get));
    }

    // Inductive form: pending_req ~> inductive_current_state_matches(sub_resource).
    // TODO: prove. The chain is analogous to pending_req ~> resource_state_matches above,
    // but the post-state additionally needs the ongoing-reconcile invariants captured by
    // inductive_current_state_matches at the AfterKRequestStep / Done states.
    assume(spec.entails(
        lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id))
            .leads_to(lift_state(inductive_current_state_matches(rabbitmq, sub_resource, controller_id)))
    ));
}

#[verifier(spinoff_prover)]
proof fn lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        sub_resource_needs_cm_rv(sub_resource) ==> // additionally requires cm_rv tracking
            spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
                }
            ).leads_to(lift_state(at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, rabbitmq, controller_id)))
        ),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let pre = |s: ClusterState| {
        &&& !s.resources().contains_key(resource_key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
    };
    let post = at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, rabbitmq, controller_id);
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& !sub_resource_needs_cm_rv(sub_resource) || cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    if !sub_resource_needs_cm_rv(sub_resource) {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    } else {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                if input->0 == req_msg {
                    let resp_msg = lemma_get_sub_resource_request_returns_ok_or_not_found(
                        s, s_prime, rabbitmq, cluster, controller_id, sub_resource, req_msg
                    );
                    assert(s_prime.in_flight().contains(resp_msg));
                } else {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                        s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0
                    );
                    if sub_resource_needs_cm_rv(sub_resource) {
                        lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                            s, s_prime, rabbitmq, cluster, controller_id, SubResource::ServerConfigMap, input->0
                        );
                    }
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
        implies post(s_prime) by {
        let resp_msg = lemma_get_sub_resource_request_returns_ok_or_not_found(
            s, s_prime, rabbitmq, cluster, controller_id, sub_resource, req_msg
        );
        assert(s_prime.in_flight().contains(resp_msg));
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

proof fn lemma_from_after_get_resource_step_to_after_create_resource_step_by_controller(
    controller_id: int,  cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message,
    s: ClusterState, s_prime: ClusterState
)
requires
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(rabbitmq.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    resp_msg_is_the_in_flight_not_found_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s),
ensures
    pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq, controller_id)(s_prime),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    match sub_resource {
        SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
        SubResource::Service => ServiceView::marshal_preserves_integrity(),
        SubResource::ErlangCookieSecret => SecretView::marshal_preserves_integrity(),
        SubResource::DefaultUserSecret => SecretView::marshal_preserves_integrity(),
        SubResource::PluginsConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServerConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServiceAccount => ServiceAccountView::marshal_preserves_integrity(),
        SubResource::Role => RoleView::marshal_preserves_integrity(),
        SubResource::RoleBinding => RoleBindingView::marshal_preserves_integrity(),
        SubResource::VStatefulSetView => VStatefulSetView::marshal_preserves_integrity(),
    }
    let step = after_create_k_request_step(sub_resource);
    let msg = s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
    let req = msg.content.get_create_request();
    assert(at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s_prime));
    assert(Cluster::has_pending_k8s_api_req_msg(controller_id, s_prime, rabbitmq.object_ref()));
    assert(s_prime.in_flight().contains(msg));
    assert(msg.src == HostId::Controller(controller_id, rabbitmq.object_ref()));
    assert(resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
    assert(req_obj_matches_sub_resource_requirements(sub_resource, rabbitmq, msg.content.get_create_request().obj)(s_prime)) by {
        let obj = msg.content.get_create_request().obj;
        if sub_resource == SubResource::VStatefulSetView {
            let cm_key = make_server_config_map_key(rabbitmq);
            let cm_obj = s.resources()[cm_key];
            let made_sts = make_sts_pass_state_validation(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version->0));
            let req_obj_spec = VStatefulSetView::unmarshal(obj)->Ok_0.spec;
            assert(VStatefulSetView::unmarshal(obj) is Ok);
            assert(VStatefulSetView::unmarshal(obj)->Ok_0.state_validation());
            assert(obj.metadata.labels == made_sts.metadata.labels);
            assert(obj.metadata.annotations == made_sts.metadata.annotations);
            assert(req_obj_spec.template == made_sts.spec.template);
        }
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_from_after_get_resource_step_to_after_create_resource_step(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        sub_resource_needs_cm_rv(sub_resource) ==> // additionally requires cm_rv tracking
            spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_not_found_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg))
                .leads_to(lift_state(pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq, controller_id)))
        ),
{
    let pre = resp_msg_is_the_in_flight_not_found_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg);
    let post = pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq, controller_id);
    let key = rabbitmq.object_ref();
    let input = (Some(resp_msg), Some(key));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& !sub_resource_needs_cm_rv(sub_resource) || cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    if !sub_resource_needs_cm_rv(sub_resource) {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    } else {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                    s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0
                );
                if sub_resource_needs_cm_rv(sub_resource) {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                        s, s_prime, rabbitmq, cluster, controller_id, SubResource::ServerConfigMap, input->0
                    );
                }
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.2 == Some(key) {
                    lemma_from_after_get_resource_step_to_after_create_resource_step_by_controller(
                        controller_id, cluster, sub_resource, rabbitmq, resp_msg, s, s_prime
                    );
                }
            }
            _ => {}
        }
    }

    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post);
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(200))]
proof fn lemma_resource_state_matches_at_after_create_resource_step(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        sub_resource_needs_cm_rv(sub_resource) ==> // additionally requires cm_rv tracking
            spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
                }
            ).leads_to(
                lift_state(resource_state_matches(sub_resource, rabbitmq))
                .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)))
            )
        ),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let pre = |s: ClusterState| {
        &&& !s.resources().contains_key(resource_key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& !sub_resource_needs_cm_rv(sub_resource) || cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    if !sub_resource_needs_cm_rv(sub_resource) {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    } else {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    }

    let post = |s: ClusterState| {
        &&& resource_state_matches(sub_resource, rabbitmq)(s)
        &&& at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)(s)
    };

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let resp = lemma_create_sub_resource_request_returns_ok(
            s, s_prime, rabbitmq, cluster, controller_id, sub_resource, pending_msg
        );
        assert(s_prime.in_flight().contains(resp));
    }

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg.src != HostId::Controller(controller_id, rabbitmq.object_ref()) {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, msg);
                    if sub_resource_needs_cm_rv(sub_resource) {
                        lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, SubResource::ServerConfigMap, msg);
                    }
                    assert(pre(s_prime));
                } else {
                    lemma_create_sub_resource_request_returns_ok(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, msg);
                    assert(post(s_prime));
                }
            },
            _ => {},
        }
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
    temp_pred_equality(
        lift_state(post),
        lift_state(resource_state_matches(sub_resource, rabbitmq))
            .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)))
    );
}

proof fn lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        sub_resource_needs_cm_rv(sub_resource) ==> // additionally requires cm_rv tracking
            spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
                }
            ).leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)))
        ),
{
    let pre = |s: ClusterState| {
        &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
    };
    let post = at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id);
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& !sub_resource_needs_cm_rv(sub_resource) || cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    if !sub_resource_needs_cm_rv(sub_resource) {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    } else {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                if input->0 == req_msg {
                    let resp_msg = lemma_get_sub_resource_request_returns_ok_or_not_found(
                        s, s_prime, rabbitmq, cluster, controller_id, sub_resource, req_msg
                    );
                    assert(s_prime.in_flight().contains(resp_msg));
                } else {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                        s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0
                    );
                    if sub_resource_needs_cm_rv(sub_resource) {
                        lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, SubResource::ServerConfigMap, input->0);
                    }
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
        implies post(s_prime) by {
        let resp_msg = lemma_get_sub_resource_request_returns_ok_or_not_found(
            s, s_prime, rabbitmq, cluster, controller_id, sub_resource, req_msg
        );
        assert(s_prime.in_flight().contains(resp_msg));
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
pub proof fn lemma_from_after_get_resource_step_to_after_update_resource_step_by_controller(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message,
    s: ClusterState, s_prime: ClusterState
)
requires
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(rabbitmq.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s_prime),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s),
ensures
    pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq, controller_id)(s_prime),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    match sub_resource {
        SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
        SubResource::Service => ServiceView::marshal_preserves_integrity(),
        SubResource::ErlangCookieSecret => SecretView::marshal_preserves_integrity(),
        SubResource::DefaultUserSecret => SecretView::marshal_preserves_integrity(),
        SubResource::PluginsConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServerConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServiceAccount => ServiceAccountView::marshal_preserves_integrity(),
        SubResource::Role => RoleView::marshal_preserves_integrity(),
        SubResource::RoleBinding => RoleBindingView::marshal_preserves_integrity(),
        SubResource::VStatefulSetView => VStatefulSetView::marshal_preserves_integrity(),
    }
    assert(s.resources() == s_prime.resources());
    let step = after_update_k_request_step(sub_resource);
    let msg = s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
    let req = msg.content.get_get_then_update_request();
    let returned_obj = resp_msg.content.get_get_response().res->Ok_0;
    let obj = msg.content.get_get_then_update_request().obj;
    if sub_resource == SubResource::VStatefulSetView {
        let cm_key = make_server_config_map_key(rabbitmq);
        let cm_obj = s.resources()[cm_key];
        let found_sts = VStatefulSetView::unmarshal(returned_obj).unwrap();
        let updated_sts = update_sts_pass_state_validation(rabbitmq, found_sts, int_to_string_view(cm_obj.metadata.resource_version->0));
        let made_sts = make_stateful_set(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version->0));
        let req_obj_spec = VStatefulSetView::unmarshal(obj)->Ok_0.spec;
        assert(VStatefulSetView::unmarshal(obj) is Ok);
        assert(VStatefulSetView::unmarshal(obj)->Ok_0.state_validation());
        assert(obj.metadata.labels == made_sts.metadata.labels);
        assert(obj.metadata.annotations == made_sts.metadata.annotations);
        assert(req_obj_spec.template == made_sts.spec.template);
    }
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
proof fn lemma_from_after_get_resource_step_to_after_update_resource_step(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message
)
    requires
        
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        sub_resource_needs_cm_rv(sub_resource) ==> // additionally requires cm_rv tracking
            spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg))
                .leads_to(lift_state(pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq, controller_id)))
        ),
{
    let pre = resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg);
    let post = pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq, controller_id);
    let input = (Some(resp_msg), Some(rabbitmq.object_ref()));
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s_prime)
        &&& !sub_resource_needs_cm_rv(sub_resource) || cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)));
    if !sub_resource_needs_cm_rv(sub_resource) {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource))),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    } else {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource))),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    }

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0);
                if sub_resource_needs_cm_rv(sub_resource) {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, SubResource::ServerConfigMap, input->0);
                }
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.2 == Some(rabbitmq.object_ref()) {
                    lemma_from_after_get_resource_step_to_after_update_resource_step_by_controller(
                        controller_id, cluster, spec, sub_resource, rabbitmq, resp_msg, s, s_prime
                    );
                } else {
                    assert(pre(s_prime));
                }
            }
            _ => {},
        }
    }

    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next,
        ControllerStep::ContinueReconcile, pre, post
    );
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
proof fn lemma_resource_state_matches_at_after_update_resource_step(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        sub_resource_needs_cm_rv(sub_resource) ==> // additionally requires cm_rv tracking
            spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, req_msg))
                .leads_to(
                    lift_state(resource_state_matches(sub_resource, rabbitmq))
                        .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)))
                )
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, req_msg);
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s_prime)
        &&& !sub_resource_needs_cm_rv(sub_resource) || cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)));
    if !sub_resource_needs_cm_rv(sub_resource) {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource))),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    } else {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource))),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    }

    let post = |s: ClusterState| {
        &&& resource_state_matches(sub_resource, rabbitmq)(s)
        &&& at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)(s)
    };

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let resp_msg = lemma_get_then_update_sub_resource_request_returns_ok(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, req_msg);
        assert(s_prime.in_flight().contains(resp_msg));
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                if input->0 != req_msg {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0);
                    if sub_resource_needs_cm_rv(sub_resource) {
                        lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, SubResource::ServerConfigMap, input->0);
                    }
                } else {
                    let resp_msg = lemma_get_then_update_sub_resource_request_returns_ok(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, req_msg);
                    assert(s_prime.in_flight().contains(resp_msg));
                }
            },
            _ => {},
        }
    }

    cluster.lemma_pre_leads_to_post_by_api_server(spec, input, stronger_next, APIServerStep::HandleRequest, pre, post);
    temp_pred_equality(
        lift_state(post),
        lift_state(resource_state_matches(sub_resource, rabbitmq))
            .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)))
    );
}

proof fn lemma_from_after_update_resource_step_to_after_get_next_resource_step(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, next_resource: SubResource, rabbitmq: RabbitmqClusterView,
    resp_msg: Message
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
    sub_resource_needs_cm_rv(sub_resource) ==> // additionally requires cm_rv tracking
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)))),
    spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    next_resource_step_after(sub_resource) == after_get_k_request_step(next_resource),
ensures
    // Bundles resource_state_matches in both pre and post: csm holds the moment we
    // see the ok update response, and the controller step into next_get does not
    // touch s.resources(), so csm is preserved.
    spec.entails(
        lift_state(|s: ClusterState| {
            &&& resource_state_matches(sub_resource, rabbitmq)(s)
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s)
        })
            .leads_to(lift_state(|s: ClusterState| {
                &&& resource_state_matches(sub_resource, rabbitmq)(s)
                &&& pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id)(s)
            }))
    )
{
    let pre = |s: ClusterState| {
        &&& resource_state_matches(sub_resource, rabbitmq)(s)
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s)
    };
    let post = |s: ClusterState| {
        &&& resource_state_matches(sub_resource, rabbitmq)(s)
        &&& pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id)(s)
    };
    let key = rabbitmq.object_ref();
    let input = (Some(resp_msg), Some(key));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s_prime)
        &&& !sub_resource_needs_cm_rv(sub_resource) || cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)));
    if !sub_resource_needs_cm_rv(sub_resource) {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource))),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    } else {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource))),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match sub_resource {
            SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
            SubResource::Service => ServiceView::marshal_preserves_integrity(),
            SubResource::ErlangCookieSecret => SecretView::marshal_preserves_integrity(),
            SubResource::DefaultUserSecret => SecretView::marshal_preserves_integrity(),
            SubResource::PluginsConfigMap => ConfigMapView::marshal_preserves_integrity(),
            SubResource::ServerConfigMap => ConfigMapView::marshal_preserves_integrity(),
            SubResource::ServiceAccount => ServiceAccountView::marshal_preserves_integrity(),
            SubResource::Role => RoleView::marshal_preserves_integrity(),
            SubResource::RoleBinding => RoleBindingView::marshal_preserves_integrity(),
            SubResource::VStatefulSetView => VStatefulSetView::marshal_preserves_integrity(),
        }
        match step {
            Step::APIServerStep(input) => {
                lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                    s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0
                );
                if sub_resource_needs_cm_rv(sub_resource) {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                        s, s_prime, rabbitmq, cluster, controller_id, SubResource::ServerConfigMap, input->0
                    );
                }
                assert(s_prime.in_flight().contains(resp_msg));
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.2 == Some(key) {
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    RabbitmqClusterView::marshal_preserves_integrity();
                    // Controller step does not touch s.resources(), so resource_state_matches preserved.
                    assert(s.resources() == s_prime.resources());
                }
            }
            _ => {}
        }
    }

    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next,
        ControllerStep::ContinueReconcile, pre, post
    );
}

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
proof fn lemma_from_after_create_resource_step_to_after_get_next_resource_step(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, next_resource: SubResource, rabbitmq: RabbitmqClusterView,
    resp_msg: Message
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
    sub_resource_needs_cm_rv(sub_resource) ==> // additionally requires cm_rv tracking
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)))),
    spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    next_resource_step_after(sub_resource) == after_get_k_request_step(next_resource) || next_resource_step_after(sub_resource) == RabbitmqReconcileStep::Done,
ensures
    next_resource_step_after(sub_resource) == after_get_k_request_step(next_resource) ==>
        spec.entails(lift_state(|s: ClusterState| {
            &&& resource_state_matches(sub_resource, rabbitmq)(s)
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s)
        })
        .leads_to(lift_state(|s: ClusterState| {
            &&& inductive_current_state_matches(rabbitmq, sub_resource, controller_id)(s)
            &&& pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id)(s)
        }))),
    next_resource_step_after(sub_resource) == RabbitmqReconcileStep::Done ==> // SubResource::VStatefulSetView
        spec.entails(lift_state(|s: ClusterState| {
            &&& resource_state_matches(sub_resource, rabbitmq)(s)
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s)
        }).leads_to(lift_state(inductive_current_state_matches(rabbitmq, sub_resource, controller_id)))),
{
    let pre = |s: ClusterState| {
        &&& resource_state_matches(sub_resource, rabbitmq)(s)
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s)
    };
    let post = if next_resource_step_after(sub_resource) == after_get_k_request_step(next_resource) {
        |s: ClusterState| {
            &&& inductive_current_state_matches(rabbitmq, sub_resource, controller_id)(s)
            &&& pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id)(s)
        }
    } else {
        inductive_current_state_matches(rabbitmq, sub_resource, controller_id)
    };
    let key = rabbitmq.object_ref();
    let input = (Some(resp_msg), Some(key));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s_prime)
        &&& !sub_resource_needs_cm_rv(sub_resource) || cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    always_to_always_later(spec, lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)));
    if !sub_resource_needs_cm_rv(sub_resource) {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource))),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    } else {
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
            later(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource))),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match sub_resource {
            SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
            SubResource::Service => ServiceView::marshal_preserves_integrity(),
            SubResource::ErlangCookieSecret => SecretView::marshal_preserves_integrity(),
            SubResource::DefaultUserSecret => SecretView::marshal_preserves_integrity(),
            SubResource::PluginsConfigMap => ConfigMapView::marshal_preserves_integrity(),
            SubResource::ServerConfigMap => ConfigMapView::marshal_preserves_integrity(),
            SubResource::ServiceAccount => ServiceAccountView::marshal_preserves_integrity(),
            SubResource::Role => RoleView::marshal_preserves_integrity(),
            SubResource::RoleBinding => RoleBindingView::marshal_preserves_integrity(),
            SubResource::VStatefulSetView => VStatefulSetView::marshal_preserves_integrity(),
        }
        match step {
            Step::APIServerStep(input) => {
                lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                    s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0
                );
                if sub_resource == SubResource::ServerConfigMap || sub_resource_needs_cm_rv(sub_resource) {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                        s, s_prime, rabbitmq, cluster, controller_id, SubResource::ServerConfigMap, input->0
                    );
                }
                assert(s_prime.in_flight().contains(resp_msg));
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.2 == Some(key) {
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    RabbitmqClusterView::marshal_preserves_integrity();
                    assert(s.resources() == s_prime.resources());
                }
            },
            _ => {},
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        RabbitmqReconcileState::marshal_preserves_integrity();
        RabbitmqClusterView::marshal_preserves_integrity();
    }

    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next,
        ControllerStep::ContinueReconcile, pre, post
    );
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
// don't touch as long as it works
pub proof fn lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_during_controller_step(
    controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView,
    s: ClusterState, s_prime: ClusterState, input: (int, Option<Message>, Option<ObjectRef>)
)
requires
    cluster.next_step(s, s_prime, Step::ControllerStep(input)),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s_prime),
    rmq_rely_conditions(cluster, controller_id)(s),
    inductive_current_state_matches(rabbitmq, sub_resource, controller_id)(s),
ensures
    inductive_current_state_matches(rabbitmq, sub_resource, controller_id)(s_prime),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    match sub_resource {
        SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
        SubResource::Service => ServiceView::marshal_preserves_integrity(),
        SubResource::ErlangCookieSecret => SecretView::marshal_preserves_integrity(),
        SubResource::DefaultUserSecret => SecretView::marshal_preserves_integrity(),
        SubResource::PluginsConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServerConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServiceAccount => ServiceAccountView::marshal_preserves_integrity(),
        SubResource::Role => RoleView::marshal_preserves_integrity(),
        SubResource::RoleBinding => RoleBindingView::marshal_preserves_integrity(),
        SubResource::VStatefulSetView => VStatefulSetView::marshal_preserves_integrity(),
    }

    let resource_key = get_request(sub_resource, rabbitmq).key;
    let cr_key = rabbitmq.object_ref();
    let cm_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let new_msgs = s_prime.in_flight().sub(s.in_flight());

    // Controller steps do not touch etcd resources.
    assert(s.resources() == s_prime.resources());
    assert(resource_state_matches(sub_resource, rabbitmq)(s_prime));

    if s.ongoing_reconciles(controller_id).contains_key(cr_key) && input.0 == controller_id && input.2 == Some(cr_key) {
        let local_state = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
        let local_state_prime = RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
        match local_state.reconcile_step {
            RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, some_resource) => {
                if some_resource == sub_resource {
                    let resp_msg = input.1->0;
                    assert(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s));
                    lemma_from_after_get_resource_step_to_after_update_resource_step_by_controller(
                        controller_id, cluster, true_pred(), sub_resource, rabbitmq, resp_msg, s, s_prime
                    );
                    assert(pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq, controller_id)(s_prime));
                } else {
                    match local_state_prime.reconcile_step {
                        RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, some_resource) => {
                            if some_resource == SubResource::ServerConfigMap {
                                // prove the response is not in flight yet
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                                assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                                assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg));
                                assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
                                    && (forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id)
                                    && s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)
                                    && msg != req_msg
                                    implies msg.rpc_id != req_msg.rpc_id by {
                                    if !s.in_flight().contains(msg) {} // need this to invoke trigger.
                                }
                            }
                        },
                        RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, _) => {
                            assert(s.resources().contains_key(resource_key));
                            if some_resource == SubResource::ServerConfigMap {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                                assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                                assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg));
                                assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
                                    && (forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id)
                                    && s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)
                                    && msg != req_msg
                                    implies msg.rpc_id != req_msg.rpc_id by {
                                    if !s.in_flight().contains(msg) {}
                                }
                            }
                        },
                        _ => {},
                    }
                }
            },
            RabbitmqReconcileStep::Init | RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, _) | RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, _) => {
                if let RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, next_resource) = local_state_prime.reconcile_step {
                    if s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg is Some {
                        if sub_resource_needs_cm_rv(next_resource) {
                            if next_resource == SubResource::ServiceAccount { // first state in sub_resource_needs_cm_rv, prove rv can be obtained from response
                                let resp_msg = input.1->0;
                                let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                                assert(s.in_flight().contains(resp_msg)); // trigger
                                if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, SubResource::ServerConfigMap) {
                                    assert(resource_create_request_msg(cm_key)(req_msg));
                                    assert(resp_msg.src is APIServer);
                                    assert(resp_msg_matches_req_msg(resp_msg, req_msg));
                                    if resp_msg.content.get_create_response().res is Ok {
                                        assert(resp_msg.content.get_create_response().res->Ok_0.metadata.resource_version == s.resources()[cm_key].metadata.resource_version);
                                    } else {
                                        assert(local_state_prime.reconcile_step == RabbitmqReconcileStep::Error);
                                        assert(false);
                                    }
                                } else if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, SubResource::ServerConfigMap) {
                                    assert(resource_get_then_update_request_msg(cm_key)(req_msg));
                                    assert(resp_msg_matches_req_msg(resp_msg, req_msg));
                                    if resp_msg.content.get_get_then_update_response().res is Ok {
                                        assert(s.resources().contains_key(cm_key));
                                        assert(resp_msg.content.get_get_then_update_response().res->Ok_0.metadata.resource_version == s.resources()[cm_key].metadata.resource_version);
                                    } else {
                                        assert(local_state_prime.reconcile_step == RabbitmqReconcileStep::Error);
                                        assert(false);
                                    }
                                } else {
                                    assert(false);
                                }
                                ConfigMapView::marshal_preserves_metadata();
                                assert(local_state_prime.latest_config_map_rv_opt == Some(int_to_string_view(s.resources()[cm_key].metadata.resource_version->0)));
                                assert(s.resources()[cm_key] == s_prime.resources()[cm_key]);
                                assert(s_prime.resources().contains_key(cm_key));
                            } else { // inherits the rv from local state
                                if let RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, current_resource) = local_state.reconcile_step {
                                    assert(sub_resource_needs_cm_rv(current_resource));
                                    assert(local_state_prime.latest_config_map_rv_opt == local_state.latest_config_map_rv_opt);
                                    assert(local_state_prime.latest_config_map_rv_opt == Some(int_to_string_view(s_prime.resources()[cm_key].metadata.resource_version->0)));
                                    assert(s_prime.resources().contains_key(cm_key));
                                } else if let RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, current_resource) = local_state.reconcile_step {
                                    assert(sub_resource_needs_cm_rv(current_resource));
                                    assert(local_state_prime.latest_config_map_rv_opt == local_state.latest_config_map_rv_opt);
                                    assert(local_state_prime.latest_config_map_rv_opt == Some(int_to_string_view(s_prime.resources()[cm_key].metadata.resource_version->0)));
                                    assert(s_prime.resources().contains_key(cm_key));
                                } else {
                                    assert(false);
                                }
                            }
                        }
                        assert(at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, next_resource))(s_prime));
                        // response is not in flight yet
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                        assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                        assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg));
                        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
                            && (forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id)
                            && s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)
                            && msg != req_msg
                            implies msg.rpc_id != req_msg.rpc_id by {
                            if !s.in_flight().contains(msg) {} // need this to invoke trigger.
                        }
                        if let RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, next_resource) = local_state_prime.reconcile_step {}
                    }
                }
            },
            _ => {},
        }
    } else if !s.ongoing_reconciles(controller_id).contains_key(cr_key) {
        if s_prime.ongoing_reconciles(controller_id).contains_key(cr_key) {} // RunScheduledReconcile inserts at Init step with no pending request.
    } else {
        // same controller_id, different CR
        assert(s.ongoing_reconciles(controller_id)[cr_key] == s_prime.ongoing_reconciles(controller_id)[cr_key]);
        assert(s.resources().contains_key(cm_key) == s_prime.resources().contains_key(cm_key));
        assert(s.resources()[cm_key] == s_prime.resources()[cm_key]);
        let local_state = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
        // all 3 forall quantifiers are maintained
        if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource) {
            let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
            assert forall |msg| {
                &&& #[trigger] s_prime.in_flight().contains(msg)
                &&& msg.src is APIServer
                &&& resp_msg_matches_req_msg(msg, pending_req)
            } implies resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, msg)(s_prime) by {
                if !new_msgs.contains(msg) {
                    assert(s.in_flight().contains(msg));
                }
            }
        }
        if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, SubResource::ServerConfigMap) {
            let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
            assert forall |msg| {
                &&& #[trigger] s_prime.in_flight().contains(msg)
                &&& msg.src is APIServer
                &&& resp_msg_matches_req_msg(msg, pending_req)
                &&& msg.content.get_get_then_update_response().res is Ok
            } implies s.resources().contains_key(cm_key)
                && msg.content.get_get_then_update_response().res->Ok_0.metadata.resource_version == s.resources()[cm_key].metadata.resource_version by {
                if !new_msgs.contains(msg) {
                    assert(s.in_flight().contains(msg));
                }
            }
        }
        if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, SubResource::ServerConfigMap) {
            let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
            assert forall |msg| {
                &&& #[trigger] s_prime.in_flight().contains(msg)
                &&& msg.src is APIServer
                &&& resp_msg_matches_req_msg(msg, pending_req)
                &&& msg.content.get_create_response().res is Ok
            } implies s.resources().contains_key(cm_key)
                && msg.content.get_create_response().res->Ok_0.metadata.resource_version == s.resources()[cm_key].metadata.resource_version by {
                if !new_msgs.contains(msg) {
                    assert(s.in_flight().contains(msg));
                }
            }
        }
    }
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
pub proof fn lemma_inductive_current_state_matches_preserves_from_s_to_s_prime(
    controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView,
    s: ClusterState, s_prime: ClusterState
)
requires
    cluster.next()(s, s_prime),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    rmq_rely_conditions(cluster, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s_prime),
    inductive_current_state_matches(rabbitmq, sub_resource, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s_prime),
    // prove CM RV does not change
    inductive_current_state_matches(rabbitmq, SubResource::ServerConfigMap, controller_id)(s),
ensures
    inductive_current_state_matches(rabbitmq, sub_resource, controller_id)(s_prime),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    match sub_resource {
        SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
        SubResource::Service => ServiceView::marshal_preserves_integrity(),
        SubResource::ErlangCookieSecret => SecretView::marshal_preserves_integrity(),
        SubResource::DefaultUserSecret => SecretView::marshal_preserves_integrity(),
        SubResource::PluginsConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServerConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServiceAccount => ServiceAccountView::marshal_preserves_integrity(),
        SubResource::Role => RoleView::marshal_preserves_integrity(),
        SubResource::RoleBinding => RoleBindingView::marshal_preserves_integrity(),
        SubResource::VStatefulSetView => VStatefulSetView::marshal_preserves_integrity(),
    }

    let resource_key = get_request(sub_resource, rabbitmq).key;
    let cm_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let cr_key = rabbitmq.object_ref();

    let step = choose |step| cluster.next_step(s, s_prime, step);
    let new_msgs = s_prime.in_flight().sub(s.in_flight());
    let local_state = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.ongoing_reconciles(controller_id) == s_prime.ongoing_reconciles(controller_id));
            if msg.src != HostId::Controller(controller_id, cr_key) {
                lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                    s, s_prime, rabbitmq, cluster, controller_id, sub_resource, msg
                );
                lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                    s, s_prime, rabbitmq, cluster, controller_id, SubResource::ServerConfigMap, msg
                );
                assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                assert(resource_state_matches(sub_resource, rabbitmq)(s_prime));
                // maintains 3 forall quantifier
                if s.ongoing_reconciles(controller_id).contains_key(cr_key) {
                    if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource) {
                        let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                        assert forall |msg| {
                            &&& #[trigger] s_prime.in_flight().contains(msg)
                            &&& msg.src is APIServer
                            &&& resp_msg_matches_req_msg(msg, pending_req)
                        } implies resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, msg)(s_prime) by {
                            if !new_msgs.contains(msg) {
                                assert(s.in_flight().contains(msg));
                            }
                        }
                    }
                    if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, SubResource::ServerConfigMap) {
                        let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                        assert(pending_req.src == HostId::Controller(controller_id, cr_key));
                        assert forall |msg| {
                            &&& #[trigger] s_prime.in_flight().contains(msg)
                            &&& msg.src is APIServer
                            &&& resp_msg_matches_req_msg(msg, pending_req)
                            &&& msg.content.get_get_then_update_response().res is Ok
                        } implies s.resources().contains_key(cm_key)
                            && msg.content.get_get_then_update_response().res->Ok_0.metadata.resource_version == s.resources()[cm_key].metadata.resource_version by {
                            if !new_msgs.contains(msg) {
                                assert(s.in_flight().contains(msg));
                            } else {
                                assert(resp_msg_matches_req_msg(msg, input->0));
                                assert(false); // violates resp_msg_matches_req_msg
                            }
                        }
                    }
                    if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, SubResource::ServerConfigMap) {
                        let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                        assert(pending_req.src == HostId::Controller(controller_id, cr_key));
                        assert forall |msg| {
                            &&& #[trigger] s_prime.in_flight().contains(msg)
                            &&& msg.src is APIServer
                            &&& resp_msg_matches_req_msg(msg, pending_req)
                            &&& msg.content.get_create_response().res is Ok
                        } implies s.resources().contains_key(cm_key)
                            && msg.content.get_create_response().res->Ok_0.metadata.resource_version == s.resources()[cm_key].metadata.resource_version by {
                            if !new_msgs.contains(msg) {
                                assert(s.in_flight().contains(msg));
                            } else {
                                assert(resp_msg_matches_req_msg(msg, input->0));
                                assert(false); // violates resp_msg_matches_req_msg
                            }
                        }
                    }
                }
            } else if s.ongoing_reconciles(controller_id).contains_key(cr_key) {
                // API server can return expected response for requests below
                match local_state.reconcile_step {
                    RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, some_resource) => {
                        if some_resource == sub_resource {
                            let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                            assert forall |msg| {
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& msg.src is APIServer
                                &&& resp_msg_matches_req_msg(msg, pending_req)
                            } implies resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, msg)(s_prime) by {
                                if !new_msgs.contains(msg) {
                                    assert(s.in_flight().contains(msg));
                                } else {
                                    let resp_msg = lemma_get_sub_resource_request_returns_ok_or_not_found(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, pending_req);
                                    assert(s_prime.in_flight().contains(resp_msg));
                                }
                            }
                        }
                    },
                    RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, some_resource) => {
                        if some_resource == SubResource::ServerConfigMap { // Update to CM is noop
                            let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                            assert(resource_get_then_update_request_msg(cm_key)(pending_req));
                            // get then update gets the most recent resource version of cm in etcd
                            assert forall |msg| {
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& msg.src is APIServer
                                &&& resp_msg_matches_req_msg(msg, pending_req)
                                &&& msg.content.get_get_then_update_response().res is Ok
                            } implies s_prime.resources().contains_key(cm_key)
                                && msg.content.get_get_then_update_response().res->Ok_0.metadata.resource_version == s_prime.resources()[cm_key].metadata.resource_version by {
                                if !new_msgs.contains(msg) {
                                    assert(s.in_flight().contains(msg));
                                }
                            }
                            // because of csm(cm), get_then_update is noop
                            ConfigMapView::marshal_preserves_integrity();
                            assert(inductive_current_state_matches(rabbitmq, SubResource::ServerConfigMap, controller_id)(s));
                            let old_obj = s.resources()[cm_key];
                            assert(old_obj.metadata.owner_references_contains(rabbitmq.controller_owner_ref())) by {
                                assert(old_obj.metadata.owner_references->0[0] == rabbitmq.controller_owner_ref());
                                assert(old_obj.metadata.owner_references->0.contains(old_obj.metadata.owner_references->0[0]));
                            }
                            assert(s_prime.resources()[cm_key] == s.resources()[cm_key]);
                        } else {
                            lemma_sub_resource_neq_implies_resource_key_neq(rabbitmq, some_resource, SubResource::ServerConfigMap);
                            assert(s_prime.resources()[cm_key] == s.resources()[cm_key]);
                        }
                        if some_resource != sub_resource {
                            lemma_sub_resource_neq_implies_resource_key_neq(rabbitmq, some_resource, sub_resource);
                            assert(s.resources()[resource_key] == s_prime.resources()[resource_key]);
                        } else {
                            assert(resource_state_matches(sub_resource, rabbitmq)(s_prime));
                        }
                    },
                    RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, some_resource) => {
                        if some_resource == SubResource::ServerConfigMap {
                            let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                            assert(resource_create_request_msg(cm_key)(pending_req));
                            assert forall |msg| {
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& msg.src is APIServer
                                &&& resp_msg_matches_req_msg(msg, pending_req)
                                &&& msg.content.get_create_response().res is Ok
                            } implies s_prime.resources().contains_key(cm_key)
                                && msg.content.get_create_response().res->Ok_0.metadata.resource_version == s_prime.resources()[cm_key].metadata.resource_version by {
                                if !new_msgs.contains(msg) {
                                    assert(s.in_flight().contains(msg));
                                } else if msg.content.get_create_response() == handle_create_request(cluster.installed_types, pending_req.content.get_create_request(), s.api_server).1 {}
                            }
                        }
                    },
                    _ => {},
                }
            }
        },
        Step::ControllerStep(input) => {
            lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_during_controller_step(
                controller_id, cluster, sub_resource, rabbitmq, s, s_prime, input
            );
        },
        _ => {
            assert(s_prime.resources() == s.resources());
            assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
            // maintains 3 forall quantifier
            if s.ongoing_reconciles(controller_id).contains_key(cr_key) {
                if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource) {
                    let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                    assert forall |msg| {
                        &&& #[trigger] s_prime.in_flight().contains(msg)
                        &&& msg.src is APIServer
                        &&& resp_msg_matches_req_msg(msg, pending_req)
                    } implies resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, msg)(s_prime) by {
                        if !new_msgs.contains(msg) {
                            assert(s.in_flight().contains(msg));
                        }
                    }
                }
                if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, SubResource::ServerConfigMap) {
                    let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                    assert forall |msg| {
                        &&& #[trigger] s_prime.in_flight().contains(msg)
                        &&& msg.src is APIServer
                        &&& resp_msg_matches_req_msg(msg, pending_req)
                        &&& msg.content.get_get_then_update_response().res is Ok
                    } implies s.resources().contains_key(cm_key)
                        && msg.content.get_get_then_update_response().res->Ok_0.metadata.resource_version == s.resources()[cm_key].metadata.resource_version by {
                        if !new_msgs.contains(msg) {
                            assert(s.in_flight().contains(msg));
                        }
                    }
                }
                if local_state.reconcile_step == RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, SubResource::ServerConfigMap) {
                    let pending_req = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                    assert forall |msg| {
                        &&& #[trigger] s_prime.in_flight().contains(msg)
                        &&& msg.src is APIServer
                        &&& resp_msg_matches_req_msg(msg, pending_req)
                        &&& msg.content.get_create_response().res is Ok
                    } implies s.resources().contains_key(cm_key)
                        && msg.content.get_create_response().res->Ok_0.metadata.resource_version == s.resources()[cm_key].metadata.resource_version by {
                        if !new_msgs.contains(msg) {
                            assert(s.in_flight().contains(msg));
                        }
                    }
                }
            }
        },
    }
}

}
