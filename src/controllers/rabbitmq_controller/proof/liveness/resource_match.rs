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
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
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
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, sub_resource: SubResource, next_resource: SubResource
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id))
            .leads_to(lift_state(resource_state_matches(sub_resource, rabbitmq)))),
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
            let resp_msg = choose |resp_msg| {
                &&& #[trigger] s.in_flight().contains(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& resp_msg.content.get_get_response().res is Ok
                &&& resp_msg.content.get_get_response().res->Ok_0 == s.resources()[key]
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
}

#[verifier(spinoff_prover)]
proof fn lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
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
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

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
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
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
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                    s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0
                );
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

    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

proof fn lemma_resource_state_matches_at_after_create_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
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
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

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
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                        s, s_prime, rabbitmq, cluster, controller_id, sub_resource, msg
                    );
                    assert(pre(s_prime));
                } else {
                    lemma_create_sub_resource_request_returns_ok(
                        s, s_prime, rabbitmq, cluster, controller_id, sub_resource, msg
                    );
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
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
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
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

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

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
proof fn lemma_resource_state_matches_at_after_update_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
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
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

    let post = |s: ClusterState| {
        &&& resource_state_matches(sub_resource, rabbitmq)(s)
        &&& at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)(s)
    };

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let resp_msg = lemma_update_sub_resource_request_returns_ok(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, req_msg);
        assert(s_prime.in_flight().contains(resp_msg));
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                if input->0 != req_msg {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0);
                } else {
                    let resp_msg = lemma_update_sub_resource_request_returns_ok(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, req_msg);
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

#[verifier(rlimit(200))]
pub proof fn lemma_from_after_get_resource_step_to_after_update_resource_step_by_controller(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message,
    s: ClusterState, s_prime: ClusterState
)
requires
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(rabbitmq.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
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
    let req = msg.content.get_update_request();
    let returned_obj = resp_msg.content.get_get_response().res->Ok_0;
    let obj = msg.content.get_update_request().obj;
    if sub_resource == SubResource::VStatefulSetView {
        let cm_key = make_server_config_map_key(rabbitmq);
        let cm_obj = s.resources()[cm_key];
        assert(returned_obj == s.resources()[returned_obj.object_ref()]);
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
#[verifier(rlimit(500))]
proof fn lemma_from_after_get_resource_step_to_after_update_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message
)
    requires
        
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
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
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0);
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
pub proof fn lemma_current_state_matches_preserves_from_s_to_s_prime(
    controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView,
    s: ClusterState, s_prime: ClusterState
)
requires
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
    cluster.next()(s, s_prime),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    cm_rv_stays_unchanged(rabbitmq)(s, s_prime),
    resource_state_matches(sub_resource, rabbitmq)(s),
ensures
    resource_state_matches(sub_resource, rabbitmq)(s_prime),
    // etcd_vsts is unchanged
    sub_resource == SubResource::VStatefulSetView ==>
        VStatefulSetView::unmarshal(s_prime.resources()[get_request(sub_resource, rabbitmq).key])->Ok_0.spec
            == VStatefulSetView::unmarshal(s.resources()[get_request(sub_resource, rabbitmq).key])->Ok_0.spec,
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let key = rabbitmq.object_ref();

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

    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)(s));
            assert(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)(s));
            assert(s.in_flight().contains(msg));
            assert(!resource_delete_request_msg(resource_key)(msg));
            assert(!resource_get_then_update_request_msg(resource_key)(msg));
            assert(!resource_get_then_delete_request_msg(resource_key)(msg));
            assert(!resource_update_status_request_msg(resource_key)(msg));
            assert(!resource_get_then_update_status_request_msg(resource_key)(msg));
            if resource_update_request_msg(resource_key)(msg) {
                if msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version {} else {
                    assert(s_prime.resources()[resource_key] == s.resources()[resource_key]);
                }
            } else {
                assert(s_prime.resources()[resource_key] == s.resources()[resource_key]);
            }
        },
        _ => {
            assert(s_prime.resources() == s.resources());
        },
    }
}


#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
pub proof fn lemma_current_state_matches_preserves_from_s_to_s_prime_for_cm(
    controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView,
    s: ClusterState, s_prime: ClusterState
)
requires
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s),
    cluster.next()(s, s_prime),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    resource_state_matches(SubResource::ServerConfigMap, rabbitmq)(s),
ensures
    resource_state_matches(SubResource::ServerConfigMap, rabbitmq)(s_prime),
    cm_rv_stays_unchanged(rabbitmq)(s, s_prime),
{
    let resource_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let key = rabbitmq.object_ref();

    RabbitmqReconcileState::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    ConfigMapView::marshal_preserves_integrity();

    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)(s));
            assert(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)(s));
            assert(s.in_flight().contains(msg));
            assert(!resource_delete_request_msg(resource_key)(msg));
            assert(!resource_get_then_update_request_msg(resource_key)(msg));
            assert(!resource_get_then_delete_request_msg(resource_key)(msg));
            assert(!resource_update_status_request_msg(resource_key)(msg));
            assert(!resource_get_then_update_status_request_msg(resource_key)(msg));
            if resource_update_request_msg(resource_key)(msg) {
                if msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version {
                    let req = msg.content.get_update_request();
                    let old_obj = s.resources()[req.key()];
                    let updated_obj = updated_object(req, old_obj);
                    assert(s.resources()[resource_key].spec == ConfigMapView::marshal_spec(make_server_config_map(rabbitmq).data));
                    assert(updated_obj == old_obj);
                    assert(s_prime.resources()[resource_key] == s.resources()[resource_key]);
                } else {
                    assert(s_prime.resources()[resource_key] == s.resources()[resource_key]);
                }
            } else {
                assert(s_prime.resources()[resource_key] == s.resources()[resource_key]);
            }
        },
        _ => {
            assert(s_prime.resources() == s.resources());
        },
    }
}

}
