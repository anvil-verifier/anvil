use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::transition_by_etcd, cluster::*, controller::types::*,
    external::state_machine::*, message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn scheduled_cr_has_lower_uid_than_uid_counter(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
        #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
            ==> s.scheduled_reconciles(controller_id)[key].metadata.uid.is_Some()
            && s.scheduled_reconciles(controller_id)[key].metadata.uid.get_Some_0() < s.api_server.uid_counter
    }
}

pub proof fn lemma_always_scheduled_cr_has_lower_uid_than_uid_counter(self, spec: TempPred<ClusterState>, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::scheduled_cr_has_lower_uid_than_uid_counter(controller_id)))),
{
    let invariant = Self::scheduled_cr_has_lower_uid_than_uid_counter(controller_id);
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, invariant);
}

pub open spec fn triggering_cr_has_lower_uid_than_uid_counter(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
        #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> s.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.uid.is_Some()
            && s.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.uid.get_Some_0() < s.api_server.uid_counter
    }
}

pub proof fn lemma_always_triggering_cr_has_lower_uid_than_uid_counter(self, spec: TempPred<ClusterState>, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::triggering_cr_has_lower_uid_than_uid_counter(controller_id)))),
{
    let invariant = Self::triggering_cr_has_lower_uid_than_uid_counter(controller_id);
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::scheduled_cr_has_lower_uid_than_uid_counter(controller_id)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_scheduled_cr_has_lower_uid_than_uid_counter(spec, controller_id);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::scheduled_cr_has_lower_uid_than_uid_counter(controller_id)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, invariant);
}

// This lemma ensures that if a controller is at some reconcile state for a cr, there must be the pending request of the
// reconcile state in flight or a corresponding response in flight.
// Obviously, this requires that when controller enters the 'state' in reconcile_core, there must be a request generated;
// otherwise, the pending request may not be there.
// The proof is very straightforward:
//   - Right after the controller enters 'state', the pending request is added to in_flight.
//   - If the pending request is processed by kubernetes api, there will be a response in flight.
//   - If the pending request is processed by external api, there will be a response in flight.
//   - If the response is processed by the controller, the controller will create a new pending request in flight which
//   allows the invariant to still hold.

pub open spec fn state_comes_with_a_pending_request(self, controller_id: int, state: spec_fn(ReconcileLocalState) -> bool) -> bool {
    &&& forall |s| #[trigger] state(s) ==> s != (self.controller_models[controller_id].reconcile_model.init)()
    &&& forall |cr, resp_o, pre_state| #[trigger] state((self.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).0) ==> (self.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).1.is_Some()
}

pub proof fn lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(self, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef, state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        self.state_comes_with_a_pending_request(controller_id, state),
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))),
    ensures spec.entails(always(lift_state(Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, state)))),
{
    let invariant = Self::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, state);
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        if Self::at_expected_reconcile_states(controller_id, key, state)(s_prime) {
            let next_step = choose |step| self.next_step(s, s_prime, step);
            let pending_req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
            let resp = choose |msg| {
                #[trigger] s.in_flight().contains(msg)
                && resp_msg_matches_req_msg(msg, pending_req_msg)
            };
            match next_step {
                Step::APIServerStep(input) => {
                    if input == Some(pending_req_msg) {
                        let resp_msg = transition_by_etcd(self.installed_types, pending_req_msg, s.api_server).1;
                        assert(s_prime.in_flight().contains(resp_msg));
                    } else {
                        if !s.in_flight().contains(pending_req_msg) {
                            assert(s_prime.in_flight().contains(resp));
                        }
                    }
                }
                Step::BuiltinControllersStep(input) => {
                    if s.in_flight().contains(pending_req_msg) {
                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0()));
                    } else {
                        assert(s_prime.in_flight().contains(resp));
                    }
                }
                Step::DropReqStep(input) => {
                    if input.0 == pending_req_msg {
                        let resp_msg = form_matched_err_resp_msg(pending_req_msg, input.1);
                        assert(s_prime.in_flight().contains(resp_msg));
                    } else {
                        if !s.in_flight().contains(pending_req_msg) {
                            assert(s_prime.in_flight().contains(resp));
                        }
                    }
                }
                Step::ControllerStep(input) => {
                    let input_controller_id = input.0;
                    let input_cr_key = input.2.get_Some_0();
                    if input_controller_id != controller_id || input_cr_key != key {
                        if s.in_flight().contains(pending_req_msg) {
                            assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0()));
                        } else {
                            assert(s_prime.in_flight().contains(resp));
                        }
                    } else {
                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0()));
                    }
                }
                Step::PodMonkeyStep(input) => {
                    if s.in_flight().contains(pending_req_msg) {
                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0()));
                    } else {
                        assert(s_prime.in_flight().contains(resp));
                    }
                }
                Step::ExternalStep(input) => {
                    if input.0 == controller_id && input.1 == Some(pending_req_msg) {
                        let resp_msg = transition_by_external(self.controller_models[controller_id].external_model.get_Some_0(), pending_req_msg, s.api_server.resources, s.controller_and_externals[controller_id].external.get_Some_0()).1;
                        assert(s_prime.in_flight().contains(resp_msg));
                    } else {
                        if !s.in_flight().contains(pending_req_msg) {
                            assert(s_prime.in_flight().contains(resp));
                        }
                    }
                }
                _ => {
                    assert(invariant(s_prime));
                }
            }
        }
    }
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant::<ClusterState>(spec, self.init(), stronger_next, invariant);
}

pub proof fn lemma_always_no_pending_req_msg_at_reconcile_state(self, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef, state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        forall |cr, resp_o, pre_state| #[trigger] state((self.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).0) ==> (self.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).1.is_None(),
    ensures spec.entails(always(lift_state(Self::no_pending_req_msg_at_reconcile_state(controller_id, key, state)))),
{
    let invariant = Self::no_pending_req_msg_at_reconcile_state(controller_id, key, state);
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) && state(s_prime.ongoing_reconciles(controller_id)[key].local_state) {
            if s.controller_and_externals[controller_id] == s_prime.controller_and_externals[controller_id] {
                assert(s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_None());
                assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.is_None());
            } else {
                assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.is_None());
            }
        }
    }
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, invariant);
}

}

}
