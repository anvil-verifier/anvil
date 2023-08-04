// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, error::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    controller::state_machine::*,
    kubernetes_api::state_machine::{handle_request, transition_by_etcd, update_is_noop},
    message::*,
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::zookeeper_controller::{
    common::ZookeeperReconcileStep,
    proof::common::*,
    spec::{reconciler::*, zookeepercluster::*},
};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates(spec: TempPred<ZKCluster>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateZKNode))),
        spec.entails(always(pending_req_is_none(zk.object_ref(), ZookeeperReconcileStep::AfterCreateZKNode))),
        spec.entails(always(pending_req_is_none(zk.object_ref(), ZookeeperReconcileStep::Init))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: ZKCluster| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let reconcile_idle = |s: ZKCluster| { !s.reconcile_state_contains(zk.object_ref()) };
    ZKCluster::lemma_reconcile_error_leads_to_reconcile_idle(spec, zk.object_ref());
    ZKCluster::lemma_reconcile_done_leads_to_reconcile_idle(spec, zk.object_ref());
    temp_pred_equality(
        lift_state(at_step(zk, ZookeeperReconcileStep::Done)),
        lift_state(ZKCluster::reconciler_reconcile_done(zk.object_ref()))
    );
    temp_pred_equality(
        lift_state(at_step(zk, ZookeeperReconcileStep::Error)),
        lift_state(ZKCluster::reconciler_reconcile_error(zk.object_ref()))
    );
    or_leads_to_combine(
        spec, at_step(zk, ZookeeperReconcileStep::Done), at_step(zk, ZookeeperReconcileStep::Error),
        reconcile_idle
    );
    temp_pred_equality(
        lift_state(at_step(zk, ZookeeperReconcileStep::Done)).or(lift_state(at_step(zk, ZookeeperReconcileStep::Error))),
        lift_state(ZKCluster::at_expected_reconcile_states(
            zk.object_ref(),
            |s: ZookeeperReconcileState| {s.reconcile_step == ZookeeperReconcileStep::Error || s.reconcile_step == ZookeeperReconcileStep::Done}
        ))
    );
    ZKCluster::lemma_from_some_state_with_ext_resp_to_two_next_states_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateZKNode,
        |s: ZookeeperReconcileState| {s.reconcile_step == ZookeeperReconcileStep::Error || s.reconcile_step == ZookeeperReconcileStep::Done}
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterUpdateStatefulSet,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateZKNode
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateStatefulSet,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateZKNode
    );

    or_leads_to_combine(
        spec, at_step(zk, ZookeeperReconcileStep::AfterUpdateStatefulSet), at_step(zk, ZookeeperReconcileStep::Error),
        reconcile_idle
    );
    temp_pred_equality(
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterUpdateStatefulSet)).or(lift_state(at_step(zk, ZookeeperReconcileStep::Error))),
        lift_state(ZKCluster::at_expected_reconcile_states(
            zk.object_ref(),
            |s: ZookeeperReconcileState| {s.reconcile_step == ZookeeperReconcileStep::AfterUpdateStatefulSet || s.reconcile_step == ZookeeperReconcileStep::Error}
        ))
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterUpdateZKNode,
        |s: ZookeeperReconcileState| {s.reconcile_step == ZookeeperReconcileStep::AfterUpdateStatefulSet || s.reconcile_step == ZookeeperReconcileStep::Error}
    );
    or_leads_to_combine_n!(
        spec,
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateStatefulSet)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterUpdateZKNode)),
        lift_state(at_step(zk, ZookeeperReconcileStep::Error));
        lift_state(reconcile_idle)
    );
    temp_pred_equality(
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateStatefulSet))
        .or(lift_state(at_step(zk, ZookeeperReconcileStep::AfterUpdateZKNode)))
        .or(lift_state(at_step(zk, ZookeeperReconcileStep::Error))),
        lift_state(ZKCluster::at_expected_reconcile_states(
            zk.object_ref(),
            |s: ZookeeperReconcileState| {
                s.reconcile_step == ZookeeperReconcileStep::AfterCreateStatefulSet
                || s.reconcile_step == ZookeeperReconcileStep::AfterUpdateZKNode
                || s.reconcile_step == ZookeeperReconcileStep::Error
            }
        ))
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterGetStatefulSet,
        |s: ZookeeperReconcileState| {
            s.reconcile_step == ZookeeperReconcileStep::AfterCreateStatefulSet
            || s.reconcile_step == ZookeeperReconcileStep::AfterUpdateZKNode
            || s.reconcile_step == ZookeeperReconcileStep::Error
        }
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateConfigMap,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterGetStatefulSet
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateAdminServerService,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateConfigMap
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateClientService,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateAdminServerService
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateHeadlessService,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateClientService
    );
    ZKCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateStatefulSet,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateZKNode
    );
    ZKCluster::lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::Init,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateHeadlessService);
    valid_implies_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(ZKCluster::reconciler_reconcile_error(zk.object_ref())),
        lift_state(at_step(zk, ZookeeperReconcileStep::Init)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateHeadlessService)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateClientService)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateAdminServerService)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateConfigMap)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterGetStatefulSet)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateStatefulSet)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterUpdateStatefulSet)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateZKNode)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterUpdateZKNode)),
        lift_state(at_step(zk, ZookeeperReconcileStep::Done));
        lift_state(reconcile_idle)
    );
}

pub open spec fn at_step(zk: ZookeeperClusterView, step: ZookeeperReconcileStep) -> StatePred<ZKCluster> {
    ZKCluster::at_expected_reconcile_states(
        zk.object_ref(), |s: ZookeeperReconcileState| s.reconcile_step == step
    )
}

pub open spec fn pending_req_or_resp_at(key: ObjectRef, step: ZookeeperReconcileStep) -> TempPred<ZKCluster> {
    lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        key, |s: ZookeeperReconcileState| s.reconcile_step == step
    ))
}

pub open spec fn pending_req_is_none(key: ObjectRef, step: ZookeeperReconcileStep) -> TempPred<ZKCluster> {
    lift_state(ZKCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(
        key, |s: ZookeeperReconcileState| s.reconcile_step == step
    ))
}

}
