// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::v2::kubernetes_cluster::spec::{
    api_server::{state_machine::transition_by_etcd, types::*},
    cluster_state_machine::*,
    controller::types::*,
    external::{state_machine::*, types::*},
    message::*,
};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn has_pending_k8s_api_req_msg(controller_id: int, s: ClusterState, key: ObjectRef) -> bool {
    &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
    &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.is_APIRequest()
}

pub open spec fn has_pending_req_msg(controller_id: int, s: ClusterState, key: ObjectRef) -> bool {
    &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
    &&& (s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.is_APIRequest()
        || s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.is_ExternalRequest())
}

pub open spec fn pending_req_msg_is(controller_id: int, s: ClusterState, key: ObjectRef, req: Message) -> bool {
    s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(req)
}

pub open spec fn no_pending_req_msg(controller_id: int, s: ClusterState, key: ObjectRef) -> bool {
    s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_None()
}

pub open spec fn at_reconcile_state(controller_id: int, key: ObjectRef, current_state: ReconcileLocalState) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.ongoing_reconciles(controller_id)[key].local_state == current_state
    }
}

pub open spec fn request_sent_by_controller(controller_id: int, msg: Message) -> bool {
    &&& msg.src == HostId::Controller(controller_id)
    &&& {
        ||| {
            &&& msg.dst == HostId::APIServer
            &&& msg.content.is_APIRequest()
        }
        ||| {
            &&& msg.dst == HostId::External(controller_id)
            &&& msg.content.is_ExternalRequest()
        }
    }
}

pub open spec fn reconciler_init_and_no_pending_req(self, controller_id: int, cr_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Self::at_reconcile_state(controller_id, cr_key, (self.reconcile_model(controller_id).init)())(s)
        &&& Self::no_pending_req_msg(controller_id, s, cr_key)
    }
}

pub open spec fn reconciler_reconcile_init(self, controller_id: int, cr_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.ongoing_reconciles(controller_id).contains_key(cr_key)
        &&& (self.reconcile_model(controller_id).init)() == s.ongoing_reconciles(controller_id)[cr_key].local_state
    }
}

pub open spec fn reconciler_reconcile_done(self, controller_id: int, cr_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.ongoing_reconciles(controller_id).contains_key(cr_key)
        &&& (self.reconcile_model(controller_id).done)(s.ongoing_reconciles(controller_id)[cr_key].local_state)
    }
}

pub open spec fn reconciler_reconcile_error(self, controller_id: int, cr_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.ongoing_reconciles(controller_id).contains_key(cr_key)
        &&& (self.reconcile_model(controller_id).error)(s.ongoing_reconciles(controller_id)[cr_key].local_state)
    }
}

pub open spec fn at_expected_reconcile_states(controller_id: int, key: ObjectRef, expected_states: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
        &&& expected_states(s.ongoing_reconciles(controller_id)[key].local_state)
    }
}

pub open spec fn no_pending_req_msg_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
            ==> Self::no_pending_req_msg(controller_id, s, key)
    }
}

pub open spec fn pending_req_in_flight_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
        &&& Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
        &&& Self::has_pending_req_msg(controller_id, s, key)
        &&& Self::request_sent_by_controller(controller_id, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool, req_msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
        &&& Self::pending_req_msg_is(controller_id, s, key, req_msg)
        &&& Self::request_sent_by_controller(controller_id, req_msg)
        &&& s.in_flight().contains(req_msg)
    }
}

pub open spec fn pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
        ==> {
            let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
            &&& Self::has_pending_req_msg(controller_id, s, key)
            &&& Self::request_sent_by_controller(controller_id, msg)
            &&& (s.in_flight().contains(msg)
                || exists |resp_msg: Message| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                })
        }
    }
}

pub open spec fn resp_in_flight_matches_pending_req_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
        &&& Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
        &&& Self::has_pending_req_msg(controller_id, s, key)
        &&& Self::request_sent_by_controller(controller_id, msg)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
        }
    }
}

pub open spec fn reconcile_idle(controller_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)
}

pub proof fn lemma_reconcile_done_leads_to_reconcile_idle(self, spec: TempPred<ClusterState>, controller_id: int, cr_key: ObjectRef)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr_key.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    ensures spec.entails(lift_state(self.reconciler_reconcile_done(controller_id, cr_key)).leads_to(lift_state(Self::reconcile_idle(controller_id, cr_key)))),
{
    let pre = self.reconciler_reconcile_done(controller_id, cr_key);
    let post = Self::reconcile_idle(controller_id, cr_key);
    let input = (None, Some(cr_key));
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    self.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::EndReconcile, pre, post);
}

pub proof fn lemma_reconcile_error_leads_to_reconcile_idle(self, spec: TempPred<ClusterState>, controller_id: int, cr_key: ObjectRef)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr_key.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    ensures spec.entails(lift_state(self.reconciler_reconcile_error(controller_id, cr_key)).leads_to(lift_state(Self::reconcile_idle(controller_id, cr_key)))),
{
    let pre = self.reconciler_reconcile_error(controller_id, cr_key);
    let post = Self::reconcile_idle(controller_id, cr_key);
    let input = (None, Some(cr_key));
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    self.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::EndReconcile, pre, post);
}

pub proof fn lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init(self, spec: TempPred<ClusterState>, controller_id: int, cr_key: ObjectRef)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr_key.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& !s.ongoing_reconciles(controller_id).contains_key(cr_key)
                &&& s.scheduled_reconciles(controller_id).contains_key(cr_key)
            }).leads_to(lift_state(self.reconciler_init_and_no_pending_req(controller_id, cr_key)))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(cr_key)
        &&& s.scheduled_reconciles(controller_id).contains_key(cr_key)
    };
    let post = self.reconciler_init_and_no_pending_req(controller_id, cr_key);
    let input = (None, Some(cr_key));
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::crash_disabled(controller_id)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::crash_disabled(controller_id)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    self.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::RunScheduledReconcile, pre, post);
}

// If given any input, current_state can transition to next_state, and next_state leads to reconcile idle,
// then current_state always leads to reconcile idle.
//
// This lemma is useful when proving reconcile termination. If we have proved that state b leads to idle,
// and state b is the successor of state a, then by applying this lemma we can get a leads to idle.
pub proof fn lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(self, spec: TempPred<ClusterState>, controller_id: int, cr: DynamicObjectView, current_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr.object_ref().kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| self.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr.object_ref())))),
        spec.entails(always(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, cr.object_ref(), current_state)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        // If external model exists, then the external state always exists.
        self.controller_models[controller_id].external_model.is_Some() ==> spec.entails(always(lift_state(Self::there_is_the_external_state(controller_id)))),
        // If external model does not exist, then there will never be any request message sent to the external system in the network.
        self.controller_models[controller_id].external_model.is_None() ==> spec.entails(always(lift_state(Self::there_is_no_request_msg_to_external(controller_id)))),
        // Current state is not the terminating state (done or error), meaning that reconcile will continue.
        forall |s| (#[trigger] current_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        // Given any input cr, resp_o and local state s, current state will transition to next state.
        forall |input_cr, resp_o, s| current_state(s) ==> #[trigger] next_state((self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
        // Next state leads to idle.
        spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state)).leads_to(lift_state(Self::reconcile_idle(controller_id, cr.object_ref())))),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), current_state)).leads_to(lift_state(Self::reconcile_idle(controller_id, cr.object_ref())))),
{
    self.lemma_from_some_state_to_arbitrary_next_state(spec, controller_id, cr, current_state, next_state);
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), current_state)),
        lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state)),
        lift_state(Self::reconcile_idle(controller_id, cr.object_ref()))
    );
}

pub proof fn lemma_from_some_state_to_arbitrary_next_state(self, spec: TempPred<ClusterState>, controller_id: int, cr: DynamicObjectView, current_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr.object_ref().kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| self.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr.object_ref())))),
        spec.entails(always(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, cr.object_ref(), current_state)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        self.controller_models[controller_id].external_model.is_Some() ==> spec.entails(always(lift_state(Self::there_is_the_external_state(controller_id)))),
        self.controller_models[controller_id].external_model.is_None() ==> spec.entails(always(lift_state(Self::there_is_no_request_msg_to_external(controller_id)))),
        forall |s| (#[trigger] current_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        forall |input_cr, resp_o, s| current_state(s) ==> #[trigger] next_state((self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), current_state)).leads_to(lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state)))),
{
    let at_some_state_and_pending_req_in_flight_or_resp_in_flight = |s: ClusterState| {
        &&& Self::at_expected_reconcile_states(controller_id, cr.object_ref(), current_state)(s)
        &&& Self::has_pending_req_msg(controller_id, s, cr.object_ref())
        &&& Self::request_sent_by_controller(controller_id, s.ongoing_reconciles(controller_id)[cr.object_ref()].pending_req_msg.get_Some_0())
        &&& (s.in_flight().contains(s.ongoing_reconciles(controller_id)[cr.object_ref()].pending_req_msg.get_Some_0())
            || exists |resp_msg: Message| {
                #[trigger] s.in_flight().contains(resp_msg)
                && resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles(controller_id)[cr.object_ref()].pending_req_msg.get_Some_0())
            })
    };
    temp_pred_equality(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, cr.object_ref(), current_state)), lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), current_state)).implies(lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight)));
    always_implies_to_leads_to(spec, lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), current_state)), lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = Self::pending_req_in_flight_at_reconcile_state(controller_id, cr.object_ref(), current_state);
    let resp_in_flight = Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state);

    self.lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state(spec, controller_id, cr, current_state, next_state);
    self.lemma_from_pending_req_in_flight_at_some_state_to_next_state(spec, controller_id, cr, current_state, next_state);

    or_leads_to_combine(spec, lift_state(req_in_flight), lift_state(resp_in_flight), lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state)));
    temp_pred_equality(lift_state(req_in_flight).or(lift_state(resp_in_flight)), lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight));
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), current_state)),
        lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state))
    );
}

pub proof fn lemma_from_init_state_to_next_state_to_reconcile_idle(self, spec: TempPred<ClusterState>, controller_id: int, cr: DynamicObjectView, init_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr.object_ref().kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::no_pending_req_msg_at_reconcile_state(controller_id, cr.object_ref(), init_state)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        forall |s| (#[trigger] init_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        forall |input_cr, resp_o, s| init_state(s) ==> next_state(#[trigger] (self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
        spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state)).leads_to(lift_state(Self::reconcile_idle(controller_id, cr.object_ref())))),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), init_state)).leads_to(lift_state(Self::reconcile_idle(controller_id, cr.object_ref())))),
{
    let no_pending_req = |s| {
        &&& Self::at_expected_reconcile_states(controller_id, cr.object_ref(), init_state)(s)
        &&& Self::no_pending_req_msg(controller_id, s, cr.object_ref())
    };
    temp_pred_equality(lift_state(Self::no_pending_req_msg_at_reconcile_state(controller_id, cr.object_ref(), init_state)), lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), init_state)).implies(lift_state(no_pending_req)));
    always_implies_to_leads_to(spec, lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), init_state)), lift_state(no_pending_req));
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::crash_disabled(controller_id)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::crash_disabled(controller_id)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    self.lemma_pre_leads_to_post_by_controller(spec, controller_id, (None, Some(cr.object_ref())), stronger_next, ControllerStep::ContinueReconcile, no_pending_req, Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state));
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), init_state)),
        lift_state(no_pending_req),
        lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state)),
        lift_state(Self::reconcile_idle(controller_id, cr.object_ref()))
    );
}

pub proof fn lemma_from_pending_req_in_flight_at_some_state_to_next_state(self, spec: TempPred<ClusterState>, controller_id: int, cr: DynamicObjectView, current_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr.object_ref().kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| self.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr.object_ref())))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        self.controller_models[controller_id].external_model.is_Some() ==> spec.entails(always(lift_state(Self::there_is_the_external_state(controller_id)))),
        self.controller_models[controller_id].external_model.is_None() ==> spec.entails(always(lift_state(Self::there_is_no_request_msg_to_external(controller_id)))),
        forall |s| (#[trigger] current_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        forall |input_cr, resp_o, s| current_state(s) ==> #[trigger] next_state((self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
    ensures spec.entails(lift_state(Self::pending_req_in_flight_at_reconcile_state(controller_id, cr.object_ref(), current_state)).leads_to(lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state)))),
{
    self.lemma_from_pending_req_in_flight_at_some_state_to_in_flight_resp_matches_pending_req_at_some_state(spec, controller_id, cr, current_state);
    self.lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state(spec, controller_id, cr, current_state, next_state);
    leads_to_trans_n!(
        spec,
        lift_state(Self::pending_req_in_flight_at_reconcile_state(controller_id, cr.object_ref(), current_state)),
        lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state)),
        lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state))
    );
}

pub proof fn lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state(self, spec: TempPred<ClusterState>, controller_id: int, cr: DynamicObjectView, current_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr.object_ref().kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr.object_ref())))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        forall |s| (#[trigger] current_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        forall |input_cr, resp_o, s| current_state(s) ==> #[trigger] next_state((self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
    ensures spec.entails(lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state)).leads_to(lift_state(Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state)))),
{
    let pre = Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state);
    let post = Self::at_expected_reconcile_states(controller_id, cr.object_ref(), next_state);
    let known_resp_in_flight = |resp| lift_state(
        |s| {
            Self::at_expected_reconcile_states(controller_id, cr.object_ref(), current_state)(s)
            && Self::has_pending_req_msg(controller_id, s, cr.object_ref())
            && Self::request_sent_by_controller(controller_id, s.ongoing_reconciles(controller_id)[cr.object_ref()].pending_req_msg.get_Some_0())
            && s.in_flight().contains(resp)
            && resp_msg_matches_req_msg(resp, s.ongoing_reconciles(controller_id)[cr.object_ref()].pending_req_msg.get_Some_0())
        }
    );
    assert forall |msg| spec.entails(#[trigger] known_resp_in_flight(msg).leads_to(lift_state(post))) by {
        let stronger_next = |s, s_prime| {
            &&& self.next()(s, s_prime)
            &&& Self::crash_disabled(controller_id)(s)
            &&& Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr.object_ref())(s)
            &&& Self::every_in_flight_msg_has_unique_id()(s)
            &&& Self::there_is_the_controller_state(controller_id)(s)
        };
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(self.next()),
            lift_state(Self::crash_disabled(controller_id)),
            lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr.object_ref())),
            lift_state(Self::every_in_flight_msg_has_unique_id()),
            lift_state(Self::there_is_the_controller_state(controller_id))
        );
        let resp_in_flight_state = |s: ClusterState| {
            Self::at_expected_reconcile_states(controller_id, cr.object_ref(), current_state)(s)
            && Self::has_pending_req_msg(controller_id, s, cr.object_ref())
            && Self::request_sent_by_controller(controller_id, s.ongoing_reconciles(controller_id)[cr.object_ref()].pending_req_msg.get_Some_0())
            && s.in_flight().contains(msg)
            && resp_msg_matches_req_msg(msg, s.ongoing_reconciles(controller_id)[cr.object_ref()].pending_req_msg.get_Some_0())
        };
        let input = (Some(msg), Some(cr.object_ref()));
        self.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, resp_in_flight_state, post);
    };
    leads_to_exists_intro(spec, known_resp_in_flight, lift_state(post));
    assert_by(
        tla_exists(known_resp_in_flight) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
            implies tla_exists(known_resp_in_flight).satisfied_by(ex) by {
                let s = ex.head();
                let msg = choose |resp_msg: Message| {
                    #[trigger] s.in_flight().contains(resp_msg)
                    && resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles(controller_id)[cr.object_ref()].pending_req_msg.get_Some_0())
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
}

pub open spec fn there_is_no_request_msg_to_external(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg)
            ==> msg.dst != HostId::External(controller_id)
    }
}

pub proof fn lemma_from_pending_req_in_flight_at_some_state_to_in_flight_resp_matches_pending_req_at_some_state(self, spec: TempPred<ClusterState>, controller_id: int, cr: DynamicObjectView, current_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr.object_ref().kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| self.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        self.controller_models[controller_id].external_model.is_Some() ==> spec.entails(always(lift_state(Self::there_is_the_external_state(controller_id)))),
        self.controller_models[controller_id].external_model.is_None() ==> spec.entails(always(lift_state(Self::there_is_no_request_msg_to_external(controller_id)))),
        forall |s| (#[trigger] current_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
    ensures spec.entails(lift_state(Self::pending_req_in_flight_at_reconcile_state(controller_id, cr.object_ref(), current_state)).leads_to(lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state)))),
{
    let pre = Self::pending_req_in_flight_at_reconcile_state(controller_id, cr.object_ref(), current_state);
    assert forall |req_msg: Message| spec.entails(
        lift_state(#[trigger] Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state, req_msg))
            .leads_to(lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state)))
    ) by {
        let pre_1 = Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state, req_msg);
        let post_1 = Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state);
        let stronger_next = |s, s_prime| {
            &&& self.next()(s, s_prime)
            &&& Self::crash_disabled(controller_id)(s)
            &&& Self::req_drop_disabled()(s)
            &&& Self::every_in_flight_msg_has_unique_id()(s)
            &&& Self::there_is_the_controller_state(controller_id)(s)
        };
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(self.next()),
            lift_state(Self::crash_disabled(controller_id)),
            lift_state(Self::req_drop_disabled()),
            lift_state(Self::every_in_flight_msg_has_unique_id()),
            lift_state(Self::there_is_the_controller_state(controller_id))
        );
        if req_msg.content.is_APIRequest() {
            let input = Some(req_msg);
            assert forall |s, s_prime| pre_1(s) && #[trigger] stronger_next(s, s_prime)
            && self.api_server_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
                let resp_msg = transition_by_etcd(self.installed_types, req_msg, s.api_server).1;
                assert({
                    &&& s_prime.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                });
            };
            assert forall |s, s_prime| pre_1(s) && #[trigger] stronger_next(s, s_prime)
            implies pre_1(s_prime) || post_1(s_prime) by {
                let step = choose |step| self.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        if input.get_Some_0() == req_msg {
                            assert(post_1(s_prime));
                        } else {
                            assert(pre_1(s_prime));
                        }
                    }
                    Step::ControllerStep(input) => { assert(pre_1(s_prime)); },
                    _ => { assert(pre_1(s_prime)); }
                }
            };
            self.lemma_pre_leads_to_post_by_api_server(spec, input, stronger_next, APIServerStep::HandleRequest, pre_1, post_1);
        } else if req_msg.content.is_ExternalRequest() {
            if self.controller_models[controller_id].external_model.is_Some() {
                let stronger_next_for_external = |s, s_prime| {
                    &&& stronger_next(s, s_prime)
                    &&& Self::there_is_the_external_state(controller_id)(s)
                };
                combine_spec_entails_always_n!(
                    spec, lift_action(stronger_next_for_external),
                    lift_action(stronger_next),
                    lift_state(Self::there_is_the_external_state(controller_id))
                );
                let input = Some(req_msg);
                assert forall |s, s_prime| pre_1(s) && #[trigger] stronger_next_for_external(s, s_prime) && self.external_next().forward((controller_id, input))(s, s_prime)
                implies post_1(s_prime) by {
                    let resp_msg = transition_by_external(self.controller_models[controller_id].external_model.get_Some_0(), req_msg, s.api_server.resources, s.controller_and_externals[controller_id].external.get_Some_0()).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    });
                };
                assert forall |s, s_prime| pre_1(s) && #[trigger] stronger_next_for_external(s, s_prime)
                implies pre_1(s_prime) || post_1(s_prime) by {
                    let step = choose |step| self.next_step(s, s_prime, step);
                    match step {
                        Step::ExternalStep(input) => {
                            if input.0 == controller_id && input.1.get_Some_0() == req_msg {
                                assert(post_1(s_prime));
                            } else {
                                assert(pre_1(s_prime));
                            }
                        }
                        Step::ControllerStep(input) => { assert(pre_1(s_prime)); },
                        _ => { assert(pre_1(s_prime)); }
                    }
                };
                self.lemma_pre_leads_to_post_by_external(spec, controller_id, input, stronger_next_for_external, ExternalStep::HandleExternalRequest, pre_1, post_1);
            } else {
                temp_pred_equality(lift_state(pre_1).and(lift_state(Self::there_is_no_request_msg_to_external(controller_id))), false_pred());
                vacuous_leads_to(spec, lift_state(pre_1), lift_state(post_1), lift_state(Self::there_is_no_request_msg_to_external(controller_id)));
                assert(spec.entails(lift_state(pre_1).leads_to(lift_state(post_1))));
            }
        } else {
            assert(spec.entails(lift_state(pre_1).leads_to(lift_state(post_1))));
        }
    }
    let msg_2_temp = |msg| lift_state(Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state, msg));
    leads_to_exists_intro(spec, msg_2_temp, lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state)));
    assert_by(
        tla_exists(|msg| lift_state(Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(controller_id, cr.object_ref(), current_state, msg))) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[cr.object_ref()].pending_req_msg.get_Some_0();
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
}

// This desired_state_is specifies the desired state (described in the cr object)
// Informally, it says that given the cr object, the object's key exists in the etcd,
// and the corresponding object in etcd has the same spec and uid of the given cr object.
// Note that we also mention the name and namespace here, which seems a bit redundant
// because it seems that lemma_always_each_object_in_etcd_is_well_formed is enough
// to tell us the name/namespace are the same between the two. Unfortunately that's not true,
// and the reason is that given option1.get_Some_0() == option2.get_Some_0() and option1.is_Some(),
// Verus cannot induce that option1.is_Some() && option1 == option2.
// So it is necessary to say both the name and namespace are also the same.
pub open spec fn desired_state_is<T: CustomResourceView>(cr: T) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resources().contains_key(cr.object_ref())
        &&& T::unmarshal(s.resources()[cr.object_ref()]).is_Ok()
        &&& T::unmarshal(s.resources()[cr.object_ref()]).get_Ok_0().metadata().name == cr.metadata().name
        &&& T::unmarshal(s.resources()[cr.object_ref()]).get_Ok_0().metadata().namespace == cr.metadata().namespace
        &&& T::unmarshal(s.resources()[cr.object_ref()]).get_Ok_0().metadata().uid == cr.metadata().uid
        &&& T::unmarshal(s.resources()[cr.object_ref()]).get_Ok_0().spec() == cr.spec()
    }
}

pub open spec fn the_object_in_schedule_has_spec_and_uid_as<T: CustomResourceView>(controller_id: int, cr: T) -> StatePred<ClusterState> {
    |s: ClusterState| s.scheduled_reconciles(controller_id).contains_key(cr.object_ref())
        ==> T::unmarshal(s.scheduled_reconciles(controller_id)[cr.object_ref()]).get_Ok_0().metadata().uid == cr.metadata().uid
        && T::unmarshal(s.scheduled_reconciles(controller_id)[cr.object_ref()]).get_Ok_0().spec() == cr.spec()
}

// This lemma says that under the spec where []desired_state_is(cr), it will eventually reach a state where any object
// in schedule for cr.object_ref() has the same spec as cr.spec.
pub proof fn lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as<T: CustomResourceView>(self, spec: TempPred<ClusterState>, controller_id: int, cr: T)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == T::kind(),
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::desired_state_is(cr)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::the_object_in_schedule_has_spec_and_uid_as(controller_id, cr))))),
{
    T::object_ref_is_well_formed();

    let stronger_pre = Self::desired_state_is(cr);
    let post = Self::the_object_in_schedule_has_spec_and_uid_as(controller_id, cr);
    let input = cr.object_ref();
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::desired_state_is(cr)(s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    always_to_always_later(spec, lift_state(Self::desired_state_is(cr)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        later(lift_state(Self::desired_state_is(cr))),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    self.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, input, stronger_next, stronger_pre, post);
    temp_pred_equality(true_pred().and(lift_state(Self::desired_state_is(cr))), lift_state(stronger_pre));
    leads_to_by_borrowing_inv(spec, true_pred(), lift_state(post), lift_state(Self::desired_state_is(cr)));
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(post));
}

pub open spec fn the_object_in_reconcile_has_spec_and_uid_as<T: CustomResourceView>(controller_id: int, cr: T) -> StatePred<ClusterState> {
    |s: ClusterState| s.ongoing_reconciles(controller_id).contains_key(cr.object_ref())
        ==> T::unmarshal(s.ongoing_reconciles(controller_id)[cr.object_ref()].triggering_cr).get_Ok_0().metadata().uid == cr.metadata().uid
        && T::unmarshal(s.ongoing_reconciles(controller_id)[cr.object_ref()].triggering_cr).get_Ok_0().spec() == cr.spec()
}

// This lemma says that under the spec where []desired_state_is(cr), it will eventually reach a state where any object
// in reconcile for cr.object_ref() has the same spec as cr.spec.
pub proof fn lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as<T: CustomResourceView>(self, spec: TempPred<ClusterState>, controller_id: int, cr: T)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == T::kind(),
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| self.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::desired_state_is(cr)))),
        spec.entails(always(lift_state(Self::the_object_in_schedule_has_spec_and_uid_as(controller_id, cr)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(true_pred().leads_to(lift_state(Self::reconcile_idle(controller_id, cr.object_ref())))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(controller_id, cr))))),
{
    T::object_ref_is_well_formed();

    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::the_object_in_schedule_has_spec_and_uid_as(controller_id, cr)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::the_object_in_schedule_has_spec_and_uid_as(controller_id, cr)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    let not_scheduled_or_reconcile = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(cr.object_ref())
        &&& !s.scheduled_reconciles(controller_id).contains_key(cr.object_ref())
    };
    let scheduled_and_not_reconcile = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(cr.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(cr.object_ref())
    };
    // Here we split the cases by whether s.scheduled_reconciles(controller_id).contains_key(cr.object_ref()) is true
    assert_by(spec.entails(lift_state(not_scheduled_or_reconcile).leads_to(lift_state(scheduled_and_not_reconcile))), {
        let input = cr.object_ref();
        let pre = not_scheduled_or_reconcile;
        let post = scheduled_and_not_reconcile;
        let stronger_pre = |s| {
            &&& pre(s)
            &&& Self::desired_state_is(cr)(s)
        };
        let even_stronger_next = |s, s_prime| {
            &&& stronger_next(s, s_prime)
            &&& Self::desired_state_is(cr)(s_prime)
        };
        always_to_always_later(spec, lift_state(Self::desired_state_is(cr)));
        combine_spec_entails_always_n!(
            spec, lift_action(even_stronger_next),
            lift_action(stronger_next),
            later(lift_state(Self::desired_state_is(cr)))
        );
        self.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, input, even_stronger_next, stronger_pre, post);
        temp_pred_equality(lift_state(pre).and(lift_state(Self::desired_state_is(cr))), lift_state(stronger_pre));
        leads_to_by_borrowing_inv(spec, lift_state(pre), lift_state(post), lift_state(Self::desired_state_is(cr)));
    });
    assert_by(spec.entails(lift_state(scheduled_and_not_reconcile).leads_to(lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(controller_id, cr)))), {
        let post = Self::the_object_in_reconcile_has_spec_and_uid_as(controller_id, cr);
        let input = (None, Some(cr.object_ref()));
        self.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::RunScheduledReconcile, scheduled_and_not_reconcile, post);
    });
    leads_to_trans(spec, lift_state(not_scheduled_or_reconcile), lift_state(scheduled_and_not_reconcile), lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(controller_id, cr)));
    let not_reconcile = Self::reconcile_idle(controller_id, cr.object_ref());
    or_leads_to_combine_and_equality!(
        spec, lift_state(not_reconcile), lift_state(scheduled_and_not_reconcile), lift_state(not_scheduled_or_reconcile);
        lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(controller_id, cr))
    );
    leads_to_trans(
        spec, true_pred(), lift_state(Self::reconcile_idle(controller_id, cr.object_ref())),
        lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(controller_id, cr))
    );
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(Self::the_object_in_reconcile_has_spec_and_uid_as(controller_id, cr)));
}

}

}
