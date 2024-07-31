// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::EmptyAPI;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::zookeeper_controller::{
    model::reconciler::*,
    proof::predicate::*,
    trusted::{spec_types::*, step::*},
};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::no_pending_req_msg_at_reconcile_state(zookeeper.object_ref(), |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::Init)))),
        spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsStatefulSet))))),
        spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsZKNode))))),
        spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKParentNode))))),
        spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKNode))))),
        spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateZKNode))))),
        spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateStatus))))),
        spec.entails(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(step.0, step.1))
        ))))),
    ensures spec.entails(true_pred().leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
{
    assert forall |action: ActionKind, sub_resource: SubResource| #![auto]
    spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(action, sub_resource))
    )))) by {
        always_tla_forall_apply::<ZKCluster, (ActionKind, SubResource)>(
            spec, |step: (ActionKind, SubResource)| lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(step.0, step.1))
            )), (action, sub_resource)
        );
    }
    let reconcile_idle = |s: ZKCluster| { !s.ongoing_reconciles().contains_key(zookeeper.object_ref()) };

    // First, prove that reconcile_done \/ reconcile_error \/ reconcile_ide ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    ZKCluster::lemma_reconcile_error_leads_to_reconcile_idle(spec, zookeeper.object_ref());
    ZKCluster::lemma_reconcile_done_leads_to_reconcile_idle(spec, zookeeper.object_ref());
    temp_pred_equality(lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Done)), lift_state(ZKCluster::reconciler_reconcile_done(zookeeper.object_ref())));
    temp_pred_equality(lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error)), lift_state(ZKCluster::reconciler_reconcile_error(zookeeper.object_ref())));
    valid_implies_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));

    or_leads_to_combine_and_equality!(spec,
        lift_state(at_step1_or_step2_state_pred(zookeeper, ZookeeperReconcileStep::Done, ZookeeperReconcileStep::Error)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Done)), lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error));
        lift_state(reconcile_idle)
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zookeeper, at_step_closure(ZookeeperReconcileStep::AfterUpdateStatus),
        at_step1_or_step2_closure(ZookeeperReconcileStep::Done, ZookeeperReconcileStep::Error)
    );
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, zookeeper, SubResource::StatefulSet, ZookeeperReconcileStep::AfterUpdateStatus);

    or_leads_to_combine_and_equality!(spec,
        lift_state(at_step1_or_step2_state_pred(zookeeper, after_get_k_request_step(SubResource::StatefulSet), ZookeeperReconcileStep::Error)),
        lift_state(at_step_state_pred(zookeeper, after_get_k_request_step(SubResource::StatefulSet))), lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error));
        lift_state(reconcile_idle)
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zookeeper, at_step_closure(ZookeeperReconcileStep::AfterUpdateZKNode),
        at_step1_or_step2_closure(after_get_k_request_step(SubResource::StatefulSet), ZookeeperReconcileStep::Error)
    );

    or_leads_to_combine_and_equality!(spec,
        lift_state(at_step1_or_step2_state_pred(zookeeper, after_get_k_request_step(SubResource::StatefulSet), ZookeeperReconcileStep::Error)),
        lift_state(at_step_state_pred(zookeeper, after_get_k_request_step(SubResource::StatefulSet))), lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error));
        lift_state(reconcile_idle)
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zookeeper, at_step_closure(ZookeeperReconcileStep::AfterCreateZKNode),
        at_step1_or_step2_closure(after_get_k_request_step(SubResource::StatefulSet), ZookeeperReconcileStep::Error)
    );

    or_leads_to_combine_and_equality!(spec,
        lift_state(at_step1_or_step2_state_pred(zookeeper, ZookeeperReconcileStep::AfterCreateZKNode, ZookeeperReconcileStep::Error)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::AfterCreateZKNode)), lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error));
        lift_state(reconcile_idle)
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zookeeper, at_step_closure(ZookeeperReconcileStep::AfterCreateZKParentNode),
        at_step1_or_step2_closure(ZookeeperReconcileStep::AfterCreateZKNode, ZookeeperReconcileStep::Error)
    );

    or_leads_to_combine_and_equality!(spec,
        lift_state(at_step1_or_step2_or_step3_state_pred(zookeeper, ZookeeperReconcileStep::AfterUpdateZKNode, ZookeeperReconcileStep::AfterCreateZKParentNode, ZookeeperReconcileStep::Error)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::AfterUpdateZKNode)), lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::AfterCreateZKParentNode)), lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error));
        lift_state(reconcile_idle)
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zookeeper, at_step_closure(ZookeeperReconcileStep::AfterExistsZKNode),
        at_step1_or_step2_or_step3_closure(ZookeeperReconcileStep::AfterUpdateZKNode, ZookeeperReconcileStep::AfterCreateZKParentNode, ZookeeperReconcileStep::Error)
    );

    or_leads_to_combine_and_equality!(spec,
        lift_state(at_step1_or_step2_or_step3_state_pred(zookeeper, ZookeeperReconcileStep::AfterExistsZKNode, after_get_k_request_step(SubResource::StatefulSet), ZookeeperReconcileStep::Error)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::AfterExistsZKNode)), lift_state(at_step_state_pred(zookeeper, after_get_k_request_step(SubResource::StatefulSet))), lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error));
        lift_state(reconcile_idle)
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zookeeper, at_step_closure(ZookeeperReconcileStep::AfterExistsStatefulSet),
        at_step1_or_step2_or_step3_closure(ZookeeperReconcileStep::AfterExistsZKNode, after_get_k_request_step(SubResource::StatefulSet), ZookeeperReconcileStep::Error)
    );

    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, zookeeper, SubResource::ConfigMap, ZookeeperReconcileStep::AfterExistsStatefulSet);
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, zookeeper, SubResource::AdminServerService, after_get_k_request_step(SubResource::ConfigMap));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, zookeeper, SubResource::ClientService, after_get_k_request_step(SubResource::AdminServerService));
    lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(spec, zookeeper, SubResource::HeadlessService, after_get_k_request_step(SubResource::ClientService));

    ZKCluster::lemma_from_init_state_to_next_state_to_reconcile_idle(spec, zookeeper, at_step_closure(ZookeeperReconcileStep::Init), at_step_closure(after_get_k_request_step(SubResource::HeadlessService)));

    // Finally, combine all cases.
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Init)),
        lift_state(state_pred_regarding_sub_resource(zookeeper, SubResource::HeadlessService)),
        lift_state(state_pred_regarding_sub_resource(zookeeper, SubResource::ClientService)),
        lift_state(state_pred_regarding_sub_resource(zookeeper, SubResource::AdminServerService)),
        lift_state(state_pred_regarding_sub_resource(zookeeper, SubResource::ConfigMap)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::AfterExistsStatefulSet)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::AfterExistsZKNode)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::AfterCreateZKParentNode)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::AfterCreateZKNode)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::AfterUpdateZKNode)),
        lift_state(state_pred_regarding_sub_resource(zookeeper, SubResource::StatefulSet)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::AfterUpdateStatus)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Done)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error));
        lift_state(reconcile_idle)
    );
}

pub open spec fn at_step1_or_step2_closure(step1: ZookeeperReconcileStep, step2: ZookeeperReconcileStep) -> spec_fn(ZookeeperReconcileState) -> bool {
    |s: ZookeeperReconcileState| s.reconcile_step == step1 || s.reconcile_step == step2
}

pub open spec fn at_step1_or_step2_or_step3_closure(step1: ZookeeperReconcileStep, step2: ZookeeperReconcileStep, step3: ZookeeperReconcileStep) -> spec_fn(ZookeeperReconcileState) -> bool {
    |s: ZookeeperReconcileState| s.reconcile_step == step1 || s.reconcile_step == step2 || s.reconcile_step == step3
}

pub open spec fn at_step_state_pred(zookeeper: ZookeeperClusterView, step: ZookeeperReconcileStep) -> StatePred<ZKCluster> {
    ZKCluster::at_expected_reconcile_states(zookeeper.object_ref(), at_step_closure(step))
}

pub open spec fn at_step1_or_step2_state_pred(zookeeper: ZookeeperClusterView, step1: ZookeeperReconcileStep, step2: ZookeeperReconcileStep) -> StatePred<ZKCluster> {
    ZKCluster::at_expected_reconcile_states(zookeeper.object_ref(), at_step1_or_step2_closure(step1, step2))
}

pub open spec fn at_step1_or_step2_or_step3_state_pred(zookeeper: ZookeeperClusterView, step1: ZookeeperReconcileStep, step2: ZookeeperReconcileStep, step3: ZookeeperReconcileStep) -> StatePred<ZKCluster> {
    ZKCluster::at_expected_reconcile_states(zookeeper.object_ref(), at_step1_or_step2_or_step3_closure(step1, step2, step3))
}

pub open spec fn state_pred_regarding_sub_resource(zookeeper: ZookeeperClusterView, sub_resource: SubResource) -> StatePred<ZKCluster> {
    ZKCluster::at_expected_reconcile_states(
        zookeeper.object_ref(),
        |s: ZookeeperReconcileState| s.reconcile_step.is_AfterKRequestStep() && s.reconcile_step.get_AfterKRequestStep_1() == sub_resource
    )
}

proof fn lemma_from_after_get_resource_step_to_after_get_next_resource_step_to_reconcile_idle(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, sub_resource: SubResource, next_step: ZookeeperReconcileStep
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        // Ensures that after get/create/update the sub resource, there is always a pending request or matched response
        // in flight so that the reconciler can enter the next state.
        forall |action: ActionKind| #![auto]
            spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(action, sub_resource)
            ))))),
        // Ensures that after successfully creating or updating the sub resource, the reconcile will go to after get next
        // sub resource step.
        next_resource_after(sub_resource) == next_step,
        spec.entails(lift_state(at_step_state_pred(zookeeper, next_step))
            .leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error))
            .leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
    ensures
        spec.entails(lift_state(at_step_state_pred(zookeeper, after_get_k_request_step(sub_resource)))
            .leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
        spec.entails(lift_state(state_pred_regarding_sub_resource(zookeeper, sub_resource))
            .leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
{
    let state_after_create_or_update = |s: ZookeeperReconcileState| {
        s.reconcile_step == next_step
        || s.reconcile_step == ZookeeperReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(ZKCluster::at_expected_reconcile_states(zookeeper.object_ref(), state_after_create_or_update)),
        lift_state(at_step_state_pred(zookeeper, next_step)),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error));
        lift_state(|s: ZKCluster| { !s.ongoing_reconciles().contains_key(zookeeper.object_ref()) })
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, zookeeper, at_step_closure(after_create_k_request_step(sub_resource)), state_after_create_or_update);
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, zookeeper, at_step_closure(after_update_k_request_step(sub_resource)), state_after_create_or_update);

    let state_after_get = |s: ZookeeperReconcileState| {
        s.reconcile_step == after_create_k_request_step(sub_resource)
        || s.reconcile_step == after_update_k_request_step(sub_resource)
        || s.reconcile_step == ZookeeperReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(ZKCluster::at_expected_reconcile_states(zookeeper.object_ref(), state_after_get)),
        lift_state(at_step_state_pred(zookeeper, after_create_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(zookeeper, after_update_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(zookeeper, ZookeeperReconcileStep::Error));
        lift_state(|s: ZKCluster| { !s.ongoing_reconciles().contains_key(zookeeper.object_ref()) })
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, zookeeper, at_step_closure(after_get_k_request_step(sub_resource)), state_after_get);
    or_leads_to_combine_and_equality!(
        spec, lift_state(state_pred_regarding_sub_resource(zookeeper, sub_resource)),
        lift_state(at_step_state_pred(zookeeper, after_get_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(zookeeper, after_create_k_request_step(sub_resource))),
        lift_state(at_step_state_pred(zookeeper, after_update_k_request_step(sub_resource)));
        lift_state(|s: ZKCluster| { !s.ongoing_reconciles().contains_key(zookeeper.object_ref()) })
    );
}

}
