use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::transition_by_etcd, types::*},
    cluster::*,
    controller::types::*,
    external::{state_machine::*, types::*},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::{map::*, prelude::*, set_lib::*};

verus! {

impl Cluster {

pub open spec fn has_pending_k8s_api_req_msg(controller_id: int, s: ClusterState, key: ObjectRef) -> bool {
    &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
    &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg->0.content is APIRequest
}

pub open spec fn has_pending_req_msg(controller_id: int, s: ClusterState, key: ObjectRef) -> bool {
    &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
    &&& (s.ongoing_reconciles(controller_id)[key].pending_req_msg->0.content is APIRequest
        || s.ongoing_reconciles(controller_id)[key].pending_req_msg->0.content is ExternalRequest)
}

pub open spec fn pending_req_msg_is(controller_id: int, s: ClusterState, key: ObjectRef, req: Message) -> bool {
    s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(req)
}

pub open spec fn no_pending_req_msg(controller_id: int, s: ClusterState, key: ObjectRef) -> bool {
    s.ongoing_reconciles(controller_id)[key].pending_req_msg is None
}

pub open spec fn at_reconcile_state(controller_id: int, key: ObjectRef, current_state: ReconcileLocalState) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.ongoing_reconciles(controller_id)[key].local_state == current_state
    }
}

pub open spec fn request_sent_by_controller(controller_id: int, msg: Message) -> bool {
    &&& msg.src.is_controller_id(controller_id)
    &&& {
        ||| {
            &&& msg.dst == HostId::APIServer
            &&& msg.content is APIRequest
        }
        ||| {
            &&& msg.dst == HostId::External(controller_id)
            &&& msg.content is ExternalRequest
        }
    }
}

pub open spec fn request_sent_by_controller_with_key(controller_id: int, key: ObjectRef, msg: Message) -> bool {
    &&& msg.src == HostId::Controller(controller_id, key)
    &&& {
        ||| {
            &&& msg.dst == HostId::APIServer
            &&& msg.content is APIRequest
        }
        ||| {
            &&& msg.dst == HostId::External(controller_id)
            &&& msg.content is ExternalRequest
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
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
        &&& Self::has_pending_req_msg(controller_id, s, key)
        &&& Self::request_sent_by_controller_with_key(controller_id, key, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool, req_msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
        &&& Self::pending_req_msg_is(controller_id, s, key, req_msg)
        &&& Self::request_sent_by_controller_with_key(controller_id, key, req_msg)
        &&& s.in_flight().contains(req_msg)
    }
}

pub open spec fn pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
        ==> {
            let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            &&& Self::has_pending_req_msg(controller_id, s, key)
            &&& Self::request_sent_by_controller_with_key(controller_id, key, msg)
            &&& (s.in_flight().contains(msg)
                || exists |resp_msg: Message| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                })
        }
    }
}

pub open spec fn pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(
    controller_id: int, key: ObjectRef
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (s.ongoing_reconciles(controller_id).contains_key(key)
        && Self::has_pending_req_msg(controller_id, s, key))
        ==> {
            let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            &&& Self::request_sent_by_controller_with_key(controller_id, key, msg)
            &&& (s.in_flight().contains(msg)
                || exists |resp_msg: Message| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                })
            &&& !(s.in_flight().contains(msg)
                && exists |resp_msg: Message| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                })
        }
    }
}

pub open spec fn resp_in_flight_matches_pending_req_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
        &&& Self::has_pending_req_msg(controller_id, s, key)
        &&& Self::request_sent_by_controller_with_key(controller_id, key, msg)
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
pub proof fn lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(self, spec: TempPred<ClusterState>, controller_id: int, cr_key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr_key.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| self.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr_key)))),
        spec.entails(always(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, cr_key, current_state)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        // If external model does not exist, then the controller never sends it request messages.
        self.controller_models[controller_id].external_model is None ==> spec.entails(always(lift_state(Self::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        // If external model exists, then the external state always exists.
        self.controller_models[controller_id].external_model is Some ==> spec.entails(always(lift_state(Self::there_is_the_external_state(controller_id)))),
        // Current state is not the terminating state (done or error), meaning that reconcile will continue.
        forall |s| (#[trigger] current_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        // Given any input cr, resp_o and local state s, current state will transition to next state.
        forall |input_cr, resp_o, s| current_state(s) ==> #[trigger] next_state((self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
        // Next state leads to idle.
        spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state)).leads_to(lift_state(Self::reconcile_idle(controller_id, cr_key)))),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, current_state)).leads_to(lift_state(Self::reconcile_idle(controller_id, cr_key)))),
{
    self.lemma_from_some_state_to_arbitrary_next_state(spec, controller_id, cr_key, current_state, next_state);
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, current_state)),
        lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state)),
        lift_state(Self::reconcile_idle(controller_id, cr_key))
    );
}

pub proof fn lemma_from_some_state_to_arbitrary_next_state(self, spec: TempPred<ClusterState>, controller_id: int, cr_key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr_key.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| self.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr_key)))),
        spec.entails(always(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, cr_key, current_state)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        self.controller_models[controller_id].external_model is None ==> spec.entails(always(lift_state(Self::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        self.controller_models[controller_id].external_model is Some ==> spec.entails(always(lift_state(Self::there_is_the_external_state(controller_id)))),
        forall |s| (#[trigger] current_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        forall |input_cr, resp_o, s| current_state(s) ==> #[trigger] next_state((self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, current_state)).leads_to(lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state)))),
{
    let at_some_state_and_pending_req_in_flight_or_resp_in_flight = |s: ClusterState| {
        &&& Self::at_expected_reconcile_states(controller_id, cr_key, current_state)(s)
        &&& Self::has_pending_req_msg(controller_id, s, cr_key)
        &&& Self::request_sent_by_controller_with_key(controller_id, cr_key, s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0)
        &&& (s.in_flight().contains(s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0)
            || exists |resp_msg: Message| {
                #[trigger] s.in_flight().contains(resp_msg)
                && resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0)
            })
    };
    temp_pred_equality(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, cr_key, current_state)), lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, current_state)).implies(lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight)));
    always_implies_to_leads_to(spec, lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, current_state)), lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = Self::pending_req_in_flight_at_reconcile_state(controller_id, cr_key, current_state);
    let resp_in_flight = Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr_key, current_state);

    self.lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state(spec, controller_id, cr_key, current_state, next_state);
    self.lemma_from_pending_req_in_flight_at_some_state_to_next_state(spec, controller_id, cr_key, current_state, next_state);

    or_leads_to_combine(spec, lift_state(req_in_flight), lift_state(resp_in_flight), lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state)));
    temp_pred_equality(lift_state(req_in_flight).or(lift_state(resp_in_flight)), lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight));
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, current_state)),
        lift_state(at_some_state_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state))
    );
}

pub proof fn lemma_from_init_state_to_next_state_to_reconcile_idle(self, spec: TempPred<ClusterState>, controller_id: int, cr_key: ObjectRef, init_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr_key.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::no_pending_req_msg_at_reconcile_state(controller_id, cr_key, init_state)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        forall |s| (#[trigger] init_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        forall |input_cr, resp_o, s| init_state(s) ==> next_state(#[trigger] (self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
        spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state)).leads_to(lift_state(Self::reconcile_idle(controller_id, cr_key)))),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, init_state)).leads_to(lift_state(Self::reconcile_idle(controller_id, cr_key)))),
{
    let no_pending_req = |s| {
        &&& Self::at_expected_reconcile_states(controller_id, cr_key, init_state)(s)
        &&& Self::no_pending_req_msg(controller_id, s, cr_key)
    };
    temp_pred_equality(lift_state(Self::no_pending_req_msg_at_reconcile_state(controller_id, cr_key, init_state)), lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, init_state)).implies(lift_state(no_pending_req)));
    always_implies_to_leads_to(spec, lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, init_state)), lift_state(no_pending_req));
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
    self.lemma_pre_leads_to_post_by_controller(spec, controller_id, (None, Some(cr_key)), stronger_next, ControllerStep::ContinueReconcile, no_pending_req, Self::at_expected_reconcile_states(controller_id, cr_key, next_state));
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, init_state)),
        lift_state(no_pending_req),
        lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state))
    );
}

pub proof fn lemma_from_some_state_to_next_state_no_req(self, spec: TempPred<ClusterState>, controller_id: int, cr_key: ObjectRef, init_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr_key.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::no_pending_req_msg_at_reconcile_state(controller_id, cr_key, init_state)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        forall |s| (#[trigger] init_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        forall |input_cr, resp_o, s| init_state(s) ==> next_state(#[trigger] (self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
    ensures spec.entails(lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, init_state)).leads_to(lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state)))),
{
    let no_pending_req = |s| {
        &&& Self::at_expected_reconcile_states(controller_id, cr_key, init_state)(s)
        &&& Self::no_pending_req_msg(controller_id, s, cr_key)
    };
    temp_pred_equality(lift_state(Self::no_pending_req_msg_at_reconcile_state(controller_id, cr_key, init_state)), lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, init_state)).implies(lift_state(no_pending_req)));
    always_implies_to_leads_to(spec, lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, init_state)), lift_state(no_pending_req));
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
    self.lemma_pre_leads_to_post_by_controller(spec, controller_id, (None, Some(cr_key)), stronger_next, ControllerStep::ContinueReconcile, no_pending_req, Self::at_expected_reconcile_states(controller_id, cr_key, next_state));
    leads_to_trans_n!(
        spec,
        lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, init_state)),
        lift_state(no_pending_req),
        lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state)),
        lift_state(Self::reconcile_idle(controller_id, cr_key))
    );
}

pub proof fn lemma_from_pending_req_in_flight_at_some_state_to_next_state(self, spec: TempPred<ClusterState>, controller_id: int, cr_key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr_key.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| self.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr_key)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        self.controller_models[controller_id].external_model is None ==> spec.entails(always(lift_state(Self::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        self.controller_models[controller_id].external_model is Some ==> spec.entails(always(lift_state(Self::there_is_the_external_state(controller_id)))),
        forall |s| (#[trigger] current_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        forall |input_cr, resp_o, s| current_state(s) ==> #[trigger] next_state((self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
    ensures spec.entails(lift_state(Self::pending_req_in_flight_at_reconcile_state(controller_id, cr_key, current_state)).leads_to(lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state)))),
{
    self.lemma_from_pending_req_in_flight_at_some_state_to_in_flight_resp_matches_pending_req_at_some_state(spec, controller_id, cr_key, current_state);
    self.lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state(spec, controller_id, cr_key, current_state, next_state);
    leads_to_trans_n!(
        spec,
        lift_state(Self::pending_req_in_flight_at_reconcile_state(controller_id, cr_key, current_state)),
        lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr_key, current_state)),
        lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state))
    );
}

pub proof fn lemma_from_in_flight_resp_matches_pending_req_at_some_state_to_next_state(self, spec: TempPred<ClusterState>, controller_id: int, cr_key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool, next_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr_key.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr_key)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        forall |s| (#[trigger] current_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
        forall |input_cr, resp_o, s| current_state(s) ==> #[trigger] next_state((self.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0),
    ensures spec.entails(lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr_key, current_state)).leads_to(lift_state(Self::at_expected_reconcile_states(controller_id, cr_key, next_state)))),
{
    let pre = Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr_key, current_state);
    let post = Self::at_expected_reconcile_states(controller_id, cr_key, next_state);
    let known_resp_in_flight = |resp| lift_state(
        |s| {
            Self::at_expected_reconcile_states(controller_id, cr_key, current_state)(s)
            && Self::has_pending_req_msg(controller_id, s, cr_key)
            && Self::request_sent_by_controller_with_key(controller_id, cr_key, s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0)
            && s.in_flight().contains(resp)
            && resp_msg_matches_req_msg(resp, s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0)
        }
    );
    assert forall |msg| spec.entails(#[trigger] known_resp_in_flight(msg).leads_to(lift_state(post))) by {
        let stronger_next = |s, s_prime| {
            &&& self.next()(s, s_prime)
            &&& Self::crash_disabled(controller_id)(s)
            &&& Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr_key)(s)
            &&& Self::every_in_flight_msg_has_unique_id()(s)
            &&& Self::there_is_the_controller_state(controller_id)(s)
        };
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(self.next()),
            lift_state(Self::crash_disabled(controller_id)),
            lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, cr_key)),
            lift_state(Self::every_in_flight_msg_has_unique_id()),
            lift_state(Self::there_is_the_controller_state(controller_id))
        );
        let resp_in_flight_state = |s: ClusterState| {
            Self::at_expected_reconcile_states(controller_id, cr_key, current_state)(s)
            && Self::has_pending_req_msg(controller_id, s, cr_key)
            && Self::request_sent_by_controller_with_key(controller_id, cr_key, s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0)
            && s.in_flight().contains(msg)
            && resp_msg_matches_req_msg(msg, s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0)
        };
        let input = (Some(msg), Some(cr_key));
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
                    && resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0)
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
}

pub open spec fn there_is_no_request_msg_to_external_from_controller(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg) // not the ideal trigger choice, but no matches for the second conjunct anymore.
            && msg.src.is_controller_id(controller_id)
            ==> msg.dst != HostId::External(controller_id)
    }
}

// this has dependency over the "no request message to external not owned by the controller",
// which will be completed in another PR on controller state machine
pub proof fn lemma_from_pending_req_in_flight_at_some_state_to_in_flight_resp_matches_pending_req_at_some_state(self, spec: TempPred<ClusterState>, controller_id: int, cr_key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr_key.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| self.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        self.controller_models[controller_id].external_model is None ==> spec.entails(always(lift_state(Self::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        self.controller_models[controller_id].external_model is Some ==> spec.entails(always(lift_state(Self::there_is_the_external_state(controller_id)))),
        forall |s| (#[trigger] current_state(s)) ==> !(self.reconcile_model(controller_id).error)(s) && !(self.reconcile_model(controller_id).done)(s),
    ensures spec.entails(lift_state(Self::pending_req_in_flight_at_reconcile_state(controller_id, cr_key, current_state)).leads_to(lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr_key, current_state)))),
{
    let pre = Self::pending_req_in_flight_at_reconcile_state(controller_id, cr_key, current_state);
    assert forall |req_msg: Message| spec.entails(
        lift_state(#[trigger] Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(controller_id, cr_key, current_state, req_msg))
            .leads_to(lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr_key, current_state)))
    ) by {
        let pre_1 = Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(controller_id, cr_key, current_state, req_msg);
        let post_1 = Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr_key, current_state);
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
        if req_msg.content is APIRequest {
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
                        if input->0 == req_msg {
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
        } else if req_msg.content is ExternalRequest {
            if self.controller_models[controller_id].external_model is Some {
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
                    let resp_msg = transition_by_external(self.controller_models[controller_id].external_model->0, req_msg, s.api_server.resources, s.controller_and_externals[controller_id].external->0).1;
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
                            if input.0 == controller_id && input.1->0 == req_msg {
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
                temp_pred_equality(lift_state(pre_1).and(lift_state(Self::there_is_no_request_msg_to_external_from_controller(controller_id))), false_pred());
                vacuous_leads_to(spec, lift_state(pre_1), lift_state(post_1), lift_state(Self::there_is_no_request_msg_to_external_from_controller(controller_id)));
                assert(spec.entails(lift_state(pre_1).leads_to(lift_state(post_1))));
            }
        } else {
            assert(spec.entails(lift_state(pre_1).leads_to(lift_state(post_1))));
        }
    }
    let msg_2_temp = |msg| lift_state(Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(controller_id, cr_key, current_state, msg));
    leads_to_exists_intro(spec, msg_2_temp, lift_state(Self::resp_in_flight_matches_pending_req_at_reconcile_state(controller_id, cr_key, current_state)));
    assert_by(
        tla_exists(|msg| lift_state(Self::req_msg_is_the_in_flight_pending_req_at_reconcile_state(controller_id, cr_key, current_state, msg))) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
}

pub open spec fn the_object_in_schedule_has_spec_and_uid_as<T: CustomResourceView>(controller_id: int, cr: T) -> StatePred<ClusterState> {
    |s: ClusterState| s.scheduled_reconciles(controller_id).contains_key(cr.object_ref())
        ==> s.scheduled_reconciles(controller_id)[cr.object_ref()].metadata.uid == cr.metadata().uid
        && T::unmarshal(s.scheduled_reconciles(controller_id)[cr.object_ref()]) is Ok
        && T::unmarshal(s.scheduled_reconciles(controller_id)[cr.object_ref()])->Ok_0.spec() == cr.spec()
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
        ==> s.ongoing_reconciles(controller_id)[cr.object_ref()].triggering_cr.metadata.uid == cr.metadata().uid
        && T::unmarshal(s.ongoing_reconciles(controller_id)[cr.object_ref()].triggering_cr) is Ok
        && T::unmarshal(s.ongoing_reconciles(controller_id)[cr.object_ref()].triggering_cr)->Ok_0.spec() == cr.spec()
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

pub open spec fn every_ongoing_reconcile_satisfies(
    controller_id: int, requirements: spec_fn(ObjectRef, ClusterState) -> bool
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
                ==> requirements(key, s) 
    }
}

pub open spec fn every_new_ongoing_reconcile_satisfies(
    controller_id: int, requirements: spec_fn(ObjectRef, ClusterState) -> bool
) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        forall |key: ObjectRef|
            {
                &&& (!s.ongoing_reconciles(controller_id).contains_key(key)
                     || requirements(key, s))
                &&& #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
            } ==> requirements(key, s_prime)
    }
}

pub open spec fn no_reconcile_before_reconcile_id_is_ongoing(controller_id: int, reconcile_id: ReconcileId) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
                ==> s.ongoing_reconciles(controller_id)[key].reconcile_id >= reconcile_id
    }
}

// This lemma shows that if spec ensures every newly started reconcile for a given controller_id
// satisfies some requirements, the system will eventually reaches a state where all ongoing reconciles
// of that controller_id satisfy those requirements.
//
// To require "every newly started reconcile for a given controller_id satisfies some requirements", 
// we use a spec_fn (i.e., a closure) as parameter which can be defined by callers and require 
// spec |= [](every_new_ongoing_reconcile_satisfies(requirements)).
pub proof fn lemma_true_leads_to_always_every_ongoing_reconcile_satisfies(
    self, 
    spec: TempPred<ClusterState>,
    controller_id: int,
    requirements: spec_fn(ObjectRef, ClusterState) -> bool
)
    requires
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        // Weak fairness for controller steps.
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        // Every new reconcile satisfies the requirements.
        spec.entails(always(lift_action(Self::every_new_ongoing_reconcile_satisfies(controller_id, requirements)))),
        // Every reconcile has lower id than allocator.
        spec.entails(always(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        // There are finitely many ongoing reconciles.
        spec.entails(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))),
        // Controller termination.
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))))),
        // There is the controller state.
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements)))))
{
    assert forall |reconcile_id| spec.entails(
        lift_state(#[trigger] Self::reconcile_id_counter_is(controller_id, reconcile_id))
                    .leads_to(always(lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements))))
    ) by {
        self.lemma_some_reconcile_id_leads_to_always_every_ongoing_reconcile_satisfies_with_reconcile_id(
            spec, controller_id, requirements, reconcile_id
        );
    }
    let has_reconcile_id = |reconcile_id| lift_state(Self::reconcile_id_counter_is(controller_id, reconcile_id));
    leads_to_exists_intro(spec, has_reconcile_id, always(lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements))));
    assert_by(
        tla_exists(has_reconcile_id) == true_pred::<ClusterState>(),
        {
            assert forall |ex| #[trigger] true_pred().satisfied_by(ex) implies tla_exists(has_reconcile_id).satisfied_by(ex) by {
                let reconcile_id = ex.head().reconcile_id_allocator(controller_id).reconcile_id_counter;
                assert(has_reconcile_id(reconcile_id).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(has_reconcile_id), true_pred());
        }
    );
}

pub proof fn lemma_some_reconcile_id_leads_to_always_every_ongoing_reconcile_satisfies_with_reconcile_id(
    self, 
    spec: TempPred<ClusterState>,
    controller_id: int,
    requirements: spec_fn(ObjectRef, ClusterState) -> bool,
    reconcile_id: ReconcileId,
)
    requires
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_action(Self::every_new_ongoing_reconcile_satisfies(controller_id, requirements)))),
        spec.entails(always(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))),
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
    ensures spec.entails(lift_state(Self::reconcile_id_counter_is(controller_id, reconcile_id))
                        .leads_to(always(lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements)))))
{
    // Use the stable part of spec, show the stability of stable_spec and also spec |= stable_spec
    let always_spec = always(lift_action(Self::every_new_ongoing_reconcile_satisfies(controller_id, requirements)))
                    .and(always(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
                    .and(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id))))
                    .and(always(lift_state(Self::there_is_the_controller_state(controller_id))))
                    .and(always(lift_action(self.next())));
    let stable_spec = always_spec.and(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1))))
                        .and(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)))));

    stable_and_always_n!(
        lift_action(Self::every_new_ongoing_reconcile_satisfies(controller_id, requirements)),
        lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Self::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Self::there_is_the_controller_state(controller_id)),
        lift_action(self.next())
    );
    self.tla_forall_controller_next_weak_fairness_is_stable(controller_id);

    // Prove termination is stable.
    let term_closure = |key: ObjectRef| lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key));
    assert forall |key: ObjectRef| #[trigger] valid(stable(true_pred().leads_to(term_closure(key)))) by {
        p_leads_to_q_is_stable(
            true_pred(),
            lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))
        );
    };
    tla_forall_a_p_leads_to_q_a_is_stable(
        true_pred(),
        |key: ObjectRef| lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)),
    );
    assert(valid(stable(tla_forall(|key: ObjectRef| true_pred().leads_to(term_closure(key))))));
    assert_by(
        tla_forall(|key: ObjectRef| true_pred().leads_to(term_closure(key)))
        == tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)))),
        {
            let lhs = tla_forall(|key: ObjectRef| true_pred().leads_to(term_closure(key)));
            let rhs = tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))));
            let lhs_inner = |key: ObjectRef| true_pred().leads_to(term_closure(key));
            let rhs_inner = |key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)));

            assert forall |ex| #[trigger] lhs.satisfied_by(ex) implies rhs.satisfied_by(ex) by {
                assert(tla_forall(lhs_inner).satisfied_by(ex));
                assert(forall |key: ObjectRef| #[trigger] lhs_inner(key).satisfied_by(ex));
                assert(forall |key: ObjectRef| lhs_inner(key).satisfied_by(ex) ==> #[trigger] rhs_inner(key).satisfied_by(ex));
                assert(tla_forall(rhs_inner).satisfied_by(ex));
            }
            assert forall |ex| #[trigger] rhs.satisfied_by(ex) implies lhs.satisfied_by(ex) by {
                assert(tla_forall(rhs_inner).satisfied_by(ex));
                assert(forall |key: ObjectRef| #[trigger] rhs_inner(key).satisfied_by(ex));
                assert(forall |key: ObjectRef| rhs_inner(key).satisfied_by(ex) ==> #[trigger] lhs_inner(key).satisfied_by(ex));
                assert(tla_forall(lhs_inner).satisfied_by(ex));
            }
            temp_pred_equality(lhs, rhs);
        }
    );

    stable_and_n!(
        always_spec, 
        tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1))),
        tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))))
    );
    entails_and_n!(
        spec,
        always(lift_action(Self::every_new_ongoing_reconcile_satisfies(controller_id, requirements))),
        always(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))),
        always(lift_state(Self::ongoing_reconciles_is_finite(controller_id))),
        always(lift_state(Self::there_is_the_controller_state(controller_id))),
        always(lift_action(self.next())),
        tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1))),
        tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))))
    );

    let spec_with_reconcile_id = stable_spec.and(lift_state(Self::reconcile_id_counter_is(controller_id, reconcile_id)));
    
    eliminate_always(spec_with_reconcile_id, lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)));

    // With reconcile_id known, we first prove that spec /\ reconcile_id |= true ~> []every_ongoing_reconcile_satisfies
    // We divide the proof into three steps:
    // (1) Prove an invariant that forall reconciles with a reconcile_id no smaller than `reconcile_id`, it satisfies the given predicate.
    // (2) Prove that spec |= true ~> []reconciles_with_lower_id_all_gone.
    // (3) With the first invariant, prove that reconciles_with_lower_id_all_gone implies all ongoing reconciles are expected.
    assert_by(
        spec_with_reconcile_id.entails(true_pred().leads_to(always(lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements))))),
        {
            self.lemma_always_has_reconcile_id_counter_no_smaller_than(spec_with_reconcile_id, controller_id, reconcile_id);
            let invariant = |s: ClusterState| {
                forall |key: ObjectRef| {
                    &&& #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
                    &&& s.ongoing_reconciles(controller_id)[key].reconcile_id >= reconcile_id
                } ==> requirements(key, s)
            };
            assert_by(
                spec_with_reconcile_id.entails(always(lift_state(invariant))),
                {
                    let init = |s: ClusterState| {
                        Self::reconcile_id_counter_is(controller_id, reconcile_id)(s)
                        && Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)(s)
                    };
                    entails_and_temp(
                        spec_with_reconcile_id, 
                        lift_state(Self::reconcile_id_counter_is(controller_id, reconcile_id)), 
                        lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))
                    );
                    temp_pred_equality(
                        lift_state(init),
                        lift_state(Self::reconcile_id_counter_is(controller_id, reconcile_id))
                            .and(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))
                    );
                    let stronger_next = |s, s_prime| {
                        self.next()(s, s_prime)
                        && Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id)(s)
                        && Self::every_new_ongoing_reconcile_satisfies(controller_id, requirements)(s, s_prime)
                        && Self::there_is_the_controller_state(controller_id)(s)
                    };

                    combine_spec_entails_always_n!(
                        spec_with_reconcile_id, lift_action(stronger_next), 
                        lift_action(self.next()),
                        lift_state(Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id)),
                        lift_action(Self::every_new_ongoing_reconcile_satisfies(controller_id, requirements)),
                        lift_state(Self::there_is_the_controller_state(controller_id))
                    );
                    init_invariant(spec_with_reconcile_id, init, stronger_next, invariant);
                }
            );

            self.lemma_true_leads_to_always_no_reconcile_before_reconcile_id_is_ongoing(
                spec_with_reconcile_id, controller_id, reconcile_id
            );           

            entails_preserved_by_always(
                lift_state(invariant),
                lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id))
                .implies(lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements)))
            );
            entails_trans(
                spec_with_reconcile_id, always(lift_state(invariant)),
                always(lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id))
                    .implies(lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements))))
            );
            always_implies_preserved_by_always(spec_with_reconcile_id, lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id)), lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements)));
            leads_to_weaken(
                spec_with_reconcile_id,
                true_pred(), always(lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id))),
                true_pred(), always(lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements)))
            );
        }
    );

    // Then unpack the condition from spec.
    unpack_conditions_from_spec(
        stable_spec, lift_state(Self::reconcile_id_counter_is(controller_id, reconcile_id)), true_pred(),
        always(lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements)))
    );
    temp_pred_equality(true_pred().and(lift_state(Self::reconcile_id_counter_is(controller_id, reconcile_id))), lift_state(Self::reconcile_id_counter_is(controller_id, reconcile_id)));
    assert(spec.entails(stable_spec));
    entails_trans(
        spec, 
        stable_spec, 
        lift_state(Self::reconcile_id_counter_is(controller_id, reconcile_id))
            .leads_to(always(lift_state(Self::every_ongoing_reconcile_satisfies(controller_id, requirements))))
    );
}

// All ongoing reconciles with a smaller id than reconcile_id will eventually terminate.
// The intuition is that (1) The number of such reconciles are bounded by rpc_id,
// and (2) weak fairness assumption ensures each message will eventually be handled by Kubernetes.
pub proof fn lemma_true_leads_to_always_no_reconcile_before_reconcile_id_is_ongoing(
    self, 
    spec: TempPred<ClusterState>,
    controller_id: int,
    reconcile_id: ReconcileId,
)
    requires
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))))),
        spec.entails(always(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id)))))
{
    self.lemma_eventually_no_reconcile_before_reconcile_id_is_ongoing(
        spec, controller_id, reconcile_id
    );

    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );

    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id)));
}

pub open spec fn ongoing_reconcile_before(controller_id: int, reconcile_id: ReconcileId, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let ongoing_reconciles = s.ongoing_reconciles(controller_id);
        ongoing_reconciles.contains_key(key) && ongoing_reconciles[key].reconcile_id < reconcile_id
    }
}

pub open spec fn ongoing_reconciles_num_is_n(controller_id: int, reconcile_id: ReconcileId, rec_num: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let ongoing_reconciles = s.ongoing_reconciles(controller_id);
        let reconciles_before_id = Map::new(
            |key| ongoing_reconciles.contains_key(key) && ongoing_reconciles[key].reconcile_id < reconcile_id,
            |key| ongoing_reconciles[key]
        );
        reconciles_before_id.dom().finite()
        && reconciles_before_id.len() == rec_num
    }
}

// need this due to controller failures
pub open spec fn ongoing_reconciles_num_is_at_most_n(controller_id: int, reconcile_id: ReconcileId, rec_num: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let ongoing_reconciles = s.ongoing_reconciles(controller_id);
        let reconciles_before_id = Map::new(
            |key| ongoing_reconciles.contains_key(key) && ongoing_reconciles[key].reconcile_id < reconcile_id,
            |key| ongoing_reconciles[key]
        );
        reconciles_before_id.dom().finite()
        && reconciles_before_id.len() <= rec_num
    }
}

pub proof fn lemma_eventually_no_reconcile_before_reconcile_id_is_ongoing(
    self, 
    spec: TempPred<ClusterState>,
    controller_id: int,
    reconcile_id: ReconcileId,
)
    requires
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))))),
        spec.entails(always(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id)))),
    ensures spec.entails(true_pred().leads_to(lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id))))
{
    let no_more_ongoing_reconciles = lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id));

    // Here we split the cases on the number of ongoing reconciles
    // and prove that for all numbers, all the reconciles will eventually terminate.
    assert forall |rec_num: nat|
        spec.entails(#[trigger] lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num))
                    .leads_to(no_more_ongoing_reconciles)) 
    by {
        self.lemma_ongoing_reconciles_num_is_n_leads_to_no_ongoing_reconciles(
            spec, controller_id, reconcile_id, rec_num
        );
    }
    leads_to_exists_intro(spec, |rec_num| lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num)), no_more_ongoing_reconciles);

    // Now we merge all the cases on different numbers of reconciles together to get true_pred()
    assert_by(spec.entails(always(true_pred().implies(tla_exists(|rec_num| lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num)))))), {
        assert forall |ex| #[trigger] spec.satisfied_by(ex) 
            implies always(true_pred().implies(tla_exists(|rec_num| lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num))))).satisfied_by(ex) by {
            assert forall |i| spec.satisfied_by(ex) && #[trigger] true_pred().satisfied_by(ex.suffix(i)) implies tla_exists(|rec_num| lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num))).satisfied_by(ex.suffix(i)) by {
                let ongoing_reconciles = ex.suffix(i).head().ongoing_reconciles(controller_id);
                let reconciles_before_id = Map::new(
                    |key| ongoing_reconciles.contains_key(key) && ongoing_reconciles[key].reconcile_id < reconcile_id,
                    |key| ongoing_reconciles[key]
                );
                let rec_num = reconciles_before_id.len();

                // machinery to prove ongoing_reconciles at dom is finite
                assert(spec.entails(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))));
                assert(forall |ex| #[trigger] spec.implies(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))).satisfied_by(ex));
                assert(spec.implies(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))).satisfied_by(ex));
                assert(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id))).satisfied_by(ex));
                assert(forall |i| #[trigger] lift_state(Self::ongoing_reconciles_is_finite(controller_id)).satisfied_by(ex.suffix(i)));
                assert(lift_state(Self::ongoing_reconciles_is_finite(controller_id)).satisfied_by(ex.suffix(i)));
                assert(ongoing_reconciles.dom().finite());

                assert(reconciles_before_id.dom().subset_of(ongoing_reconciles.dom()));
                lemma_len_subset(reconciles_before_id.dom(), ongoing_reconciles.dom());
                assert(reconciles_before_id.dom().finite());
                assert(lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num)).satisfied_by(ex.suffix(i)));
                assert((|rec_num| lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num)))(rec_num).satisfied_by(ex.suffix(i)));
                assert(tla_exists(|rec_num| lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num))).satisfied_by(ex.suffix(i)));
            }
        }
    });

    always_implies_to_leads_to(
        spec,
        true_pred(),
        tla_exists(|rec_num| lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num)))
    );

    leads_to_trans(
        spec,
        true_pred(),
        tla_exists(|rec_num| lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num))),
        lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id))
    );
}

pub proof fn lemma_ongoing_reconciles_num_is_n_leads_to_no_ongoing_reconciles(
    self, 
    spec: TempPred<ClusterState>,
    controller_id: int,
    reconcile_id: ReconcileId,
    rec_num: nat
)
    requires
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))))),
        spec.entails(always(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id)))),
    ensures 
        spec.entails(
            lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num))
            .leads_to(lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id)))
        ),
    decreases 
        rec_num
{
    if rec_num == 0 {
        // base case
        let no_more_ongoing_reconciles = Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id);

        assert_by(valid(lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, 0)).implies(lift_state(no_more_ongoing_reconciles))), {
            assert forall |s| #[trigger] Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, 0)(s) implies no_more_ongoing_reconciles(s) by {
                assert forall |key| Self::ongoing_reconcile_before(controller_id, reconcile_id, key)(s) implies !(#[trigger] s.ongoing_reconciles(controller_id).contains_key(key)) by {
                    let ongoing_reconciles = s.ongoing_reconciles(controller_id);
                    let reconciles_before_id = Map::new(
                        |key| ongoing_reconciles.contains_key(key) && ongoing_reconciles[key].reconcile_id < reconcile_id,
                        |key| ongoing_reconciles[key]
                    );
                    assert(reconciles_before_id.contains_key(key));
                    assert(reconciles_before_id.len() > 0);
                }
            }
        });

        entails_implies_leads_to(spec, lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, 0)), lift_state(no_more_ongoing_reconciles));
    } else {
        // induction step
        let no_more_ongoing_reconciles = lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id));
        let reconcile_ongoing = |key: ObjectRef| lift_state(|s: ClusterState|
            s.ongoing_reconciles(controller_id).contains_key(key) && s.ongoing_reconciles(controller_id)[key].reconcile_id < reconcile_id
        );
        let ongoing_reconciles_num_is_n_and_reconcile_ongoing = |key: ObjectRef| 
            lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num))
                .and(reconcile_ongoing(key));

        // prove that "there are rec_num reconciles" ~> "there are at most rec_num - 1 reconciles"
        assert forall |key: ObjectRef|
            spec.entails(#[trigger] ongoing_reconciles_num_is_n_and_reconcile_ongoing(key)
                        .leads_to(lift_state(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat)))) by {
            self.lemma_ongoing_reconciles_num_decreases(
                spec, controller_id, reconcile_id, rec_num, key
            );
        }
        leads_to_exists_intro(
            spec, ongoing_reconciles_num_is_n_and_reconcile_ongoing, lift_state(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat))
        );

        // merge all the cases on different keys together
        assert_by(
            tla_exists(ongoing_reconciles_num_is_n_and_reconcile_ongoing) == lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num)),
            {
                assert forall |ex| #[trigger] lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num)).satisfied_by(ex) 
                implies tla_exists(ongoing_reconciles_num_is_n_and_reconcile_ongoing).satisfied_by(ex) by {
                    let ongoing_reconciles = ex.head().ongoing_reconciles(controller_id);
                    let reconciles_before_id = Map::new(
                        |key| ongoing_reconciles.contains_key(key) && ongoing_reconciles[key].reconcile_id < reconcile_id,
                        |key| ongoing_reconciles[key]
                    );
                    let key = reconciles_before_id.dom().choose();
                    assert(reconciles_before_id.contains_key(key));
                    assert(lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num)).satisfied_by(ex));
                    assert(reconcile_ongoing(key).satisfied_by(ex));
                    assert((|key| ongoing_reconciles_num_is_n_and_reconcile_ongoing(key))(key).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(ongoing_reconciles_num_is_n_and_reconcile_ongoing), lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num)));
            }
        );

        assert_by(
            spec.entails(
                lift_state(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat))
                .leads_to(lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id)))
            ), 
            {
                assert forall |ex| #[trigger] lift_state(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat)).satisfied_by(ex)
                    implies tla_exists(|n: nat| lift_state(|s| {
                        &&& Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, n)(s)
                        &&& n < rec_num
                    })).satisfied_by(ex) by {
                    let ongoing_reconciles = ex.head().ongoing_reconciles(controller_id);
                    let reconciles_before_id = Map::new(
                        |key| ongoing_reconciles.contains_key(key) && ongoing_reconciles[key].reconcile_id < reconcile_id,
                        |key| ongoing_reconciles[key]
                    );
                    let n = reconciles_before_id.len();

                    assert(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, n)(ex.head()));
                    assert(n < rec_num);
                    assert((|s| {
                        &&& Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, n)(s)
                        &&& n < rec_num
                    })(ex.head()));
                    assert(lift_state(|s| {
                        &&& Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, n)(s)
                        &&& n < rec_num
                    }).satisfied_by(ex));
                    assert((|n: nat| lift_state(|s| {
                        &&& Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, n)(s)
                        &&& n < rec_num
                    }))(n).satisfied_by(ex));
                }

                let ongoing_reconciles_num_is_n_and_less_than_rec_num = |n: nat| lift_state(|s| {
                    &&& Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, n)(s)
                    &&& n < rec_num
                });
                entails_implies_leads_to(
                    spec, 
                    lift_state(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat)), 
                    tla_exists(ongoing_reconciles_num_is_n_and_less_than_rec_num)
                );

                assert forall |n: nat| n < rec_num implies #[trigger] spec.entails(
                    ongoing_reconciles_num_is_n_and_less_than_rec_num(n)
                    .leads_to(lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id)))) by {
                    
                    self.lemma_ongoing_reconciles_num_is_n_leads_to_no_ongoing_reconciles(
                        spec, controller_id, reconcile_id, n
                    );

                    leads_to_weaken(
                        spec, lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, n)), lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id)),
                        ongoing_reconciles_num_is_n_and_less_than_rec_num(n), lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id))
                    );
                }

                leads_to_exists_intro(
                    spec, ongoing_reconciles_num_is_n_and_less_than_rec_num, lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id))
                );

                leads_to_trans(
                    spec,
                    lift_state(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat)),
                    tla_exists(ongoing_reconciles_num_is_n_and_less_than_rec_num),
                    lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id))
                );
            }
        );
        
        leads_to_trans(
            spec, 
            lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num)),
            lift_state(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat)),
            no_more_ongoing_reconciles
        );

        assert(spec.entails(lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num))
                .leads_to(lift_state(Self::no_reconcile_before_reconcile_id_is_ongoing(controller_id, reconcile_id)))));
    }
}

pub proof fn lemma_ongoing_reconciles_num_decreases(
    self, 
    spec: TempPred<ClusterState>,
    controller_id: int,
    reconcile_id: ReconcileId,
    rec_num: nat,
    key: ObjectRef,
)
    requires
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))))),
        spec.entails(always(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id)))),
        rec_num > 0,
    ensures 
        spec.entails(
            lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num))
                .and(lift_state(|s: ClusterState| s.ongoing_reconciles(controller_id).contains_key(key) 
                    && s.ongoing_reconciles(controller_id)[key].reconcile_id < reconcile_id))
                .leads_to(lift_state(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat)))
        )
{
    let reconcile_ongoing = |key: ObjectRef| lift_state(|s: ClusterState|
        s.ongoing_reconciles(controller_id).contains_key(key) && s.ongoing_reconciles(controller_id)[key].reconcile_id < reconcile_id
    );
    let ongoing_reconciles_num_is_n_and_reconcile_ongoing = |key: ObjectRef| 
        lift_state(Self::ongoing_reconciles_num_is_n(controller_id, reconcile_id, rec_num))
            .and(reconcile_ongoing(key));


    // Set up wf1_variant_temp argument.
    let invariant = |s: ClusterState| {
        &&& Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, rec_num)(s)
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.ongoing_reconciles(controller_id)[key].reconcile_id < reconcile_id
    };

    let stronger_next = |s, s_prime| {
        self.next()(s, s_prime)
        && Self::there_is_the_controller_state(controller_id)(s)
        && Self::ongoing_reconciles_is_finite(controller_id)(s)
        && Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)(s)
        && Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id)(s)
    };

    // show spec |= [](p /\ next => p' \/ q')
    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) 
        implies invariant(s_prime) || Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat)(s_prime) by {

        let step = choose |step| self.next_step(s, s_prime, step);
        match step {
            Step::ControllerStep((id, _, key_opt)) => {
                let some_key = key_opt.unwrap();
                if id == controller_id {
                    let ongoing_reconciles = s.ongoing_reconciles(controller_id);
                    let ongoing_reconciles_prime = s_prime.ongoing_reconciles(controller_id);

                    let reconciles_before_id = Map::new(
                        |key| ongoing_reconciles.contains_key(key) && ongoing_reconciles[key].reconcile_id < reconcile_id,
                        |key| ongoing_reconciles[key]
                    );
                    let reconciles_before_id_prime = Map::new(
                        |key| ongoing_reconciles_prime.contains_key(key) && ongoing_reconciles_prime[key].reconcile_id < reconcile_id,
                        |key| ongoing_reconciles_prime[key]
                    );

                    if ongoing_reconciles_prime.len() > ongoing_reconciles.len() {
                        assert(reconciles_before_id.dom() =~= reconciles_before_id_prime.dom());
                    } else if ongoing_reconciles_prime.len() == ongoing_reconciles.len() {
                        assert(reconciles_before_id.dom() =~= reconciles_before_id_prime.dom());
                    } else {
                        assert(reconciles_before_id.dom().remove(some_key) =~= reconciles_before_id_prime.dom());
                    }
                }
            },
            Step::RestartControllerStep(id) => {
                if id == controller_id {
                    let ongoing_reconciles = s_prime.ongoing_reconciles(controller_id);
                    let reconciles_before_id = Map::new(
                        |key| ongoing_reconciles.contains_key(key) && ongoing_reconciles[key].reconcile_id < reconcile_id,
                        |key| ongoing_reconciles[key]
                    );
                    assert(ongoing_reconciles =~= reconciles_before_id);
                    assert(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat)(s_prime));
                }
            },
            _ => {}
        }
    }

    // show spec |= []next.    
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id)),
        lift_state(Self::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id))
    );

    // show spec |= []p ~> forward.
    use_tla_forall(spec, |key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))), key);
    entails_implies_leads_to(
        spec,
        always(lift_state(invariant)),
        true_pred()
    );
    leads_to_trans(
        spec,
        always(lift_state(invariant)),
        true_pred(),
        lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))
    );

    // apply wf1 argument.
    wf1_variant_temp(
        spec, lift_action(stronger_next), 
        lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)), 
        lift_state(invariant), 
        lift_state(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat))
    );

    entails_implies_leads_to(
        spec,
        ongoing_reconciles_num_is_n_and_reconcile_ongoing(key),
        lift_state(invariant)
    );
    leads_to_trans(
        spec,
        ongoing_reconciles_num_is_n_and_reconcile_ongoing(key),
        lift_state(invariant),
        lift_state(Self::ongoing_reconciles_num_is_at_most_n(controller_id, reconcile_id, (rec_num - 1) as nat))
    );
}

}

}
