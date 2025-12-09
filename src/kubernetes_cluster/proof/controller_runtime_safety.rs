use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::transition_by_etcd, cluster::*, controller::types::*,
    external::state_machine::*, message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn scheduled_cr_has_lower_uid_than_uid_counter(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
        #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
            ==> s.scheduled_reconciles(controller_id)[key].metadata.uid is Some
            && s.scheduled_reconciles(controller_id)[key].metadata.uid->0 < s.api_server.uid_counter
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
            ==> s.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.uid is Some
            && s.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.uid->0 < s.api_server.uid_counter
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
    &&& forall |cr, resp_o, pre_state| #[trigger] state((self.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).0) ==> (self.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).1 is Some
}

// TODO: Investigate flaky proof.
#[verifier(rlimit(100))]
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
            let pending_req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
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
                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
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
                    let input_cr_key = input.2->0;
                    if input_controller_id != controller_id || input_cr_key != key {
                        if s.in_flight().contains(pending_req_msg) {
                            assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                        } else {
                            assert(s_prime.in_flight().contains(resp));
                        }
                    } else {
                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                    }
                }
                Step::PodMonkeyStep(input) => {
                    if s.in_flight().contains(pending_req_msg) {
                        assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                    } else {
                        assert(s_prime.in_flight().contains(resp));
                    }
                }
                Step::ExternalStep(input) => {
                    if input.0 == controller_id && input.1 == Some(pending_req_msg) {
                        let resp_msg = transition_by_external(self.controller_models[controller_id].external_model->0, pending_req_msg, s.api_server.resources, s.controller_and_externals[controller_id].external->0).1;
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

// TODO: investigate flaky proof
#[verifier(spinoff_prover)]
#[verifier(rlimit(10))]
pub proof fn lemma_true_leads_to_always_pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(self, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef)
    requires
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))),
        spec.entails(always(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_no_replicas_and_has_unique_id()))),
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !(s.ongoing_reconciles(controller_id).contains_key(key)))))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key))))),
{
    let requirements = |ky: ObjectRef, s: ClusterState| {
        (s.ongoing_reconciles(controller_id).contains_key(key)
        && Self::has_pending_req_msg(controller_id, s, key)
        && ky == key)
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
    };
    let requirements_antecedent = |ky: ObjectRef, s: ClusterState| {
        (s.ongoing_reconciles(controller_id).contains_key(key)
        && Self::has_pending_req_msg(controller_id, s, key)
        && ky == key)
    };

    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
        &&& Self::crash_disabled(controller_id)(s)
        &&& Self::req_drop_disabled()(s)
        &&& Self::pod_monkey_disabled()(s)
        &&& Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key)(s)
        &&& Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)(s)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Self::ongoing_reconciles_is_finite(controller_id)(s)
        &&& Self::every_in_flight_msg_has_no_replicas_and_has_unique_id()(s)
    };

    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_ongoing_reconcile_satisfies(controller_id, requirements)(s, s_prime) by {
        assert forall |ky: ObjectRef| (!s.ongoing_reconciles(controller_id).contains_key(ky) || requirements(ky, s))
        && #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(ky) implies requirements(ky, s_prime) by {
            if requirements_antecedent(ky, s_prime) {
                let next_step = choose |step| self.next_step(s, s_prime, step);
                let pending_req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                let resp = choose |msg| {
                    #[trigger] s.in_flight().contains(msg)
                    && resp_msg_matches_req_msg(msg, pending_req_msg)
                };
                // The difficult part of this case splitting is showing mutual exclusion:
                // i.e., ~(A /\ \Ex.B(x)). In many places, I need to prove ~\Ex.B(x) which
                // is equivalent to \Ax.~B(x).
                // (note A: pending msg in flight, \Ex.B(x): exists response in flight).
                match next_step {
                    Step::APIServerStep(input) => {
                        if input == Some(pending_req_msg) {
                            let resp_msg = transition_by_etcd(self.installed_types, pending_req_msg, s.api_server).1;
                            assert(s_prime.in_flight().contains(resp_msg));
                            assert(!s_prime.in_flight().contains(pending_req_msg));
                        } else {
                            if !s.in_flight().contains(pending_req_msg) {
                                assert(s_prime.in_flight().contains(resp));
                                assert(!s_prime.in_flight().contains(pending_req_msg));
                            } else {
                                let req_msg = input.unwrap();
                                let resp_msg = transition_by_etcd(self.installed_types, req_msg, s.api_server).1;
                                assert(s_prime.in_flight().contains(pending_req_msg));
                                assert(pending_req_msg != req_msg);
                                assert(!resp_msg_matches_req_msg(resp_msg, pending_req_msg));
                                assert forall |resp_msg: Message| {
                                    &&& (!s.ongoing_reconciles(controller_id).contains_key(key) || requirements(key, s))
                                    &&& s.ongoing_reconciles(controller_id).contains_key(key)
                                    &&& stronger_next(s, s_prime)
                                } implies {
                                    ||| ! #[trigger] s_prime.in_flight().contains(resp_msg)
                                    ||| !resp_msg_matches_req_msg(resp_msg, pending_req_msg)
                                } by {
                                    if s.in_flight().contains(resp_msg) {}
                                }
                            }
                        }
                    }
                    Step::BuiltinControllersStep(input) => {
                        if s.in_flight().contains(pending_req_msg) {
                            assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                            assert(!exists |resp_msg: Message| {
                                &&& #[trigger] s.in_flight().contains(resp_msg)
                                &&& resp_msg_matches_req_msg(resp_msg, pending_req_msg)
                            });
                            assert forall |resp_msg: Message| {
                                &&& (!s.ongoing_reconciles(controller_id).contains_key(key) || requirements(key, s))
                                &&& s.ongoing_reconciles(controller_id).contains_key(key)
                                &&& stronger_next(s, s_prime)
                            } implies {
                                ||| ! #[trigger] s_prime.in_flight().contains(resp_msg)
                                ||| !resp_msg_matches_req_msg(resp_msg, pending_req_msg)
                            } by {
                                if s.in_flight().contains(resp_msg) {}
                            }
                        } else {
                            assert(s_prime.in_flight().contains(resp));
                            assert(!s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                        }
                    }
                    Step::ControllerStep(input) => {
                        let input_controller_id = input.0;
                        let input_cr_key = input.2->0;
                        if input_controller_id != controller_id || input_cr_key != key {
                            if s.in_flight().contains(pending_req_msg) {
                                assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                                assert(!exists |resp_msg: Message| {
                                    &&& #[trigger] s.in_flight().contains(resp_msg)
                                    &&& resp_msg_matches_req_msg(resp_msg, pending_req_msg)
                                });
                                assert forall |resp_msg: Message| {
                                    &&& (!s.ongoing_reconciles(controller_id).contains_key(key) || requirements(key, s))
                                    &&& s.ongoing_reconciles(controller_id).contains_key(key)
                                    &&& stronger_next(s, s_prime)
                                } implies {
                                    ||| ! #[trigger] s_prime.in_flight().contains(resp_msg)
                                    ||| !resp_msg_matches_req_msg(resp_msg, pending_req_msg)
                                } by {
                                    if s.in_flight().contains(resp_msg) {}
                                }
                            } else {
                                assert(s_prime.in_flight().contains(resp));
                                assert(!s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                            }
                        } else {
                            let new_pending_req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                            assert(s_prime.in_flight().contains(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                            assert forall |resp_msg: Message| {
                                &&& (!s.ongoing_reconciles(controller_id).contains_key(key) || requirements(key, s))
                                &&& s.ongoing_reconciles(controller_id).contains_key(key)
                                &&& stronger_next(s, s_prime)
                            } implies {
                                ||| ! #[trigger] s_prime.in_flight().contains(resp_msg)
                                ||| !resp_msg_matches_req_msg(resp_msg, new_pending_req_msg)
                            } by {
                                if s.in_flight().contains(resp_msg) {}
                            }
                        }
                    }
                    Step::ExternalStep(input) => {
                        if input.0 == controller_id && input.1 == Some(pending_req_msg) {
                            let resp_msg = transition_by_external(self.controller_models[controller_id].external_model->0, pending_req_msg, s.api_server.resources, s.controller_and_externals[controller_id].external->0).1;
                            assert(s_prime.in_flight().contains(resp_msg));
                            assert(!s_prime.in_flight().contains(pending_req_msg));
                        } else if input.0 == controller_id {
                            if !s.in_flight().contains(pending_req_msg) {
                                assert(s_prime.in_flight().contains(resp));
                                assert(!s_prime.in_flight().contains(pending_req_msg));
                            } else {
                                let req_msg = input.1.unwrap();
                                let resp_msg = transition_by_external(self.controller_models[controller_id].external_model->0, req_msg, s.api_server.resources, s.controller_and_externals[controller_id].external->0).1;
                                assert(s_prime.in_flight().contains(pending_req_msg));
                                assert(pending_req_msg != req_msg);
                                assert(!resp_msg_matches_req_msg(resp_msg, pending_req_msg));
                                assert forall |resp_msg: Message| {
                                    &&& (!s.ongoing_reconciles(controller_id).contains_key(key) || requirements(key, s))
                                    &&& s.ongoing_reconciles(controller_id).contains_key(key)
                                    &&& stronger_next(s, s_prime)
                                } implies {
                                    ||| ! #[trigger] s_prime.in_flight().contains(resp_msg)
                                    ||| !resp_msg_matches_req_msg(resp_msg, pending_req_msg)
                                } by {
                                    if s.in_flight().contains(resp_msg) {}
                                }
                            }
                        }
                    }
                    _ => {
                        assert(requirements(ky, s_prime));
                    }
                }
            }
        }
    }

    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_ongoing_reconcile_satisfies(controller_id, requirements)),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id)),
        lift_state(Self::crash_disabled(controller_id)),
        lift_state(Self::req_drop_disabled()),
        lift_state(Self::pod_monkey_disabled()),
        lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key)),
        lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Self::every_in_flight_msg_has_no_replicas_and_has_unique_id())
    );

    self.lemma_true_leads_to_always_every_ongoing_reconcile_satisfies(spec, controller_id, requirements);

    temp_pred_equality(
        lift_state(Self::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)),
        lift_state(Cluster::every_ongoing_reconcile_satisfies(controller_id, requirements))
    );
}

pub proof fn lemma_always_no_pending_req_msg_at_reconcile_state(self, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef, state: spec_fn(ReconcileLocalState) -> bool)
    requires
        self.controller_models.contains_key(controller_id),
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        forall |cr, resp_o, pre_state| #[trigger] state((self.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).0) ==> (self.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).1 is None,
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
                assert(s.ongoing_reconciles(controller_id)[key].pending_req_msg is None);
                assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is None);
            } else {
                assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is None);
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

pub open spec fn cr_objects_in_etcd_satisfy_state_validation<T: CustomResourceView>() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            let unmarshal_result =
                T::unmarshal(s.resources()[key]);
            #[trigger] s.resources().contains_key(key)
            && key.kind is CustomResourceKind
            && key.kind == T::kind()
            ==> unmarshal_result is Ok
                && unmarshal_result.unwrap().state_validation()
        }
    }
}

// TODO: investigate flaky proof.
#[verifier(spinoff_prover)]
pub proof fn lemma_always_cr_objects_in_etcd_satisfy_state_validation<T: CustomResourceView>(
    self, spec: TempPred<ClusterState>,
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.type_is_installed_in_cluster::<T>(),
    ensures spec.entails(always(lift_state(Self::cr_objects_in_etcd_satisfy_state_validation::<T>()))),
{
    let inv = Self::cr_objects_in_etcd_satisfy_state_validation::<T>();
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& self.each_custom_object_in_etcd_is_well_formed::<T>()(s)
    };
    self.lemma_always_each_custom_object_in_etcd_is_well_formed::<T>(spec);

    T::marshal_preserves_integrity();
    T::marshal_spec_preserves_integrity();
    T::marshal_status_preserves_integrity();
    T::unmarshal_result_determined_by_unmarshal_spec_and_status();
    T::validation_result_determined_by_spec_and_status();

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(self.each_custom_object_in_etcd_is_well_formed::<T>())
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

pub open spec fn cr_objects_in_schedule_satisfy_state_validation<T: CustomResourceView>(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            let unmarshal_result =
                T::unmarshal(s.scheduled_reconciles(controller_id)[key]);
            #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
            && key.kind is CustomResourceKind
            && key.kind == T::kind()
            ==> unmarshal_result is Ok
                && unmarshal_result.unwrap().state_validation()
        }
    }
}

pub proof fn lemma_always_cr_objects_in_schedule_satisfy_state_validation<T: CustomResourceView>(
    self, spec: TempPred<ClusterState>, controller_id: int
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.type_is_installed_in_cluster::<T>(),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::cr_objects_in_schedule_satisfy_state_validation::<T>(controller_id)))),
{
    let inv = Self::cr_objects_in_schedule_satisfy_state_validation::<T>(controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::cr_objects_in_etcd_satisfy_state_validation::<T>()(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_cr_objects_in_etcd_satisfy_state_validation::<T>(spec);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);

    T::marshal_preserves_integrity();
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::cr_objects_in_etcd_satisfy_state_validation::<T>()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

pub open spec fn cr_objects_in_reconcile_satisfy_state_validation<T: CustomResourceView>(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            let unmarshal_result =
                T::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr);
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            && key.kind is CustomResourceKind
            && key.kind == T::kind()
            ==> unmarshal_result is Ok
                && unmarshal_result.unwrap().state_validation()
        }
    }
}

pub proof fn lemma_always_cr_objects_in_reconcile_satisfy_state_validation<T: CustomResourceView>(
    self, spec: TempPred<ClusterState>, controller_id: int
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.type_is_installed_in_cluster::<T>(),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::cr_objects_in_reconcile_satisfy_state_validation::<T>(controller_id)))),
{
    let inv = Self::cr_objects_in_reconcile_satisfy_state_validation::<T>(controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::cr_objects_in_etcd_satisfy_state_validation::<T>()(s)
        &&& Self::cr_objects_in_schedule_satisfy_state_validation::<T>(controller_id)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_cr_objects_in_etcd_satisfy_state_validation::<T>(spec);
    self.lemma_always_cr_objects_in_schedule_satisfy_state_validation::<T>(spec, controller_id);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);

    T::marshal_preserves_integrity();
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::cr_objects_in_etcd_satisfy_state_validation::<T>()),
        lift_state(Self::cr_objects_in_schedule_satisfy_state_validation::<T>(controller_id)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

pub open spec fn cr_states_are_unmarshallable<S: Marshallable, K: CustomResourceView>(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            let unmarshal_result =
                S::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state);
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            && key.kind is CustomResourceKind
            && key.kind == K::kind()
            ==> unmarshal_result is Ok
        }
    }
}

pub proof fn lemma_always_cr_states_are_unmarshallable<R, S, K, EReq, EResp>(
    self, spec: TempPred<ClusterState>, controller_id: int
)
    where
        R: Reconciler<S, K, EReq, EResp>,
        K: CustomResourceView,
        S: Marshallable,
        EReq: Marshallable,
        EResp: Marshallable,
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.type_is_installed_in_cluster::<K>(),
        self.controller_models.contains_key(controller_id),
        self.controller_models[controller_id].reconcile_model == Self::installed_reconcile_model::<R, S, K, EReq, EResp>(),
    ensures spec.entails(always(lift_state(Self::cr_states_are_unmarshallable::<S, K>(controller_id)))),
{
    let inv = Self::cr_states_are_unmarshallable::<S, K>(controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);

    S::marshal_preserves_integrity();
    K::marshal_preserves_integrity();
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

pub open spec fn cr_objects_in_schedule_have_correct_kind<T: CustomResourceView>(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
            ==> key.kind == T::kind()
        }
    }
}

pub proof fn lemma_always_cr_objects_in_schedule_have_correct_kind<T: CustomResourceView>(
    self, spec: TempPred<ClusterState>, controller_id: int
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.type_is_installed_in_cluster::<T>(),
        self.controller_models.contains_key(controller_id),
        self.controller_models[controller_id].reconcile_model.kind == T::kind(),
    ensures spec.entails(always(lift_state(Self::cr_objects_in_schedule_have_correct_kind::<T>(controller_id)))),
{
    let inv = Self::cr_objects_in_schedule_have_correct_kind::<T>(controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);

    T::marshal_preserves_integrity();
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

pub open spec fn cr_objects_in_reconcile_have_correct_kind<T: CustomResourceView>(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> key.kind == T::kind()
        }
    }
}

pub proof fn lemma_always_cr_objects_in_reconcile_have_correct_kind<T: CustomResourceView>(
    self, spec: TempPred<ClusterState>, controller_id: int
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.type_is_installed_in_cluster::<T>(),
        self.controller_models.contains_key(controller_id),
        self.controller_models[controller_id].reconcile_model.kind == T::kind(),
    ensures spec.entails(always(lift_state(Self::cr_objects_in_reconcile_have_correct_kind::<T>(controller_id)))),
{
    let inv = Self::cr_objects_in_reconcile_have_correct_kind::<T>(controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
        &&& Self::cr_objects_in_schedule_have_correct_kind::<T>(controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    self.lemma_always_cr_objects_in_schedule_have_correct_kind::<T>(spec, controller_id);

    T::marshal_preserves_integrity();
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id)),
        lift_state(Self::cr_objects_in_schedule_have_correct_kind::<T>(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

pub open spec fn ongoing_reconciles_is_finite(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.ongoing_reconciles(controller_id).dom().finite()
    }
}

pub proof fn lemma_always_ongoing_reconciles_is_finite(self, spec: TempPred<ClusterState>, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::ongoing_reconciles_is_finite(controller_id)))),
{
    let invariant = Self::ongoing_reconciles_is_finite(controller_id);
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant::<ClusterState>(spec, self.init(), stronger_next, invariant);
}

pub open spec fn reconcile_id_counter_is(controller_id: int, reconcile_id: nat) -> StatePred<ClusterState> {
    |s: ClusterState| s.reconcile_id_allocator(controller_id).reconcile_id_counter == reconcile_id
}

pub open spec fn reconcile_id_counter_is_no_smaller_than(controller_id: int, reconcile_id: nat) -> StatePred<ClusterState> {
    |s: ClusterState| s.reconcile_id_allocator(controller_id).reconcile_id_counter >= reconcile_id
}

pub proof fn lemma_always_has_reconcile_id_counter_no_smaller_than(
    self, spec: TempPred<ClusterState>, controller_id: int, reconcile_id: ReconcileId
)
    requires
        spec.entails(always(lift_action(self.next()))),
        // need redundancy since the basepoint might not be init.
        self.controller_models.contains_key(controller_id),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(lift_state(Self::reconcile_id_counter_is(controller_id, reconcile_id))),
    ensures spec.entails(always(lift_state(Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id)))),
{
    let invariant = Self::reconcile_id_counter_is_no_smaller_than(controller_id, reconcile_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant::<ClusterState>(spec, Self::reconcile_id_counter_is(controller_id, reconcile_id), stronger_next, invariant);
}

pub open spec fn every_ongoing_reconcile_has_lower_id_than_allocator(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> s.ongoing_reconciles(controller_id)[key].reconcile_id
                    < s.reconcile_id_allocator(controller_id).reconcile_id_counter
    }
}

pub proof fn lemma_always_every_ongoing_reconcile_has_lower_id_than_allocator(
    self, spec: TempPred<ClusterState>, controller_id: int,
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
{
    let invariant = Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id);

    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key) implies
        s_prime.ongoing_reconciles(controller_id)[key].reconcile_id < s_prime.reconcile_id_allocator(controller_id).reconcile_id_counter by {
            let step = choose |step| self.next_step(s, s_prime, step);
            if s.ongoing_reconciles(controller_id).contains_key(key) {
                assert(s.reconcile_id_allocator(controller_id).reconcile_id_counter <= s_prime.reconcile_id_allocator(controller_id).reconcile_id_counter);
            }
        }
    };
    init_invariant::<ClusterState>(spec, self.init(), stronger_next, invariant);
}

pub open spec fn every_ongoing_reconcile_has_unique_id(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key1, key2|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key1)
            && #[trigger] s.ongoing_reconciles(controller_id).contains_key(key2)
            && key1 != key2
            ==>  s.ongoing_reconciles(controller_id)[key1].reconcile_id
                    != s.ongoing_reconciles(controller_id)[key2].reconcile_id
    }
}

pub proof fn lemma_always_every_ongoing_reconcile_has_unique_id(
    self, spec: TempPred<ClusterState>, controller_id: int,
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::every_ongoing_reconcile_has_unique_id(controller_id)))),
{
    let invariant = Self::every_ongoing_reconcile_has_unique_id(controller_id);
    let stronger_next = |s, s_prime| {
        self.next()(s, s_prime)
        && Self::there_is_the_controller_state(controller_id)(s)
        && Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    self.lemma_always_every_ongoing_reconcile_has_lower_id_than_allocator(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id)),
        lift_state(Self::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))
    );
    init_invariant::<ClusterState>(spec, self.init(), stronger_next, invariant);
}

pub open spec fn every_msg_from_key_is_pending_req_msg_of(
    controller_id: int, key: ObjectRef
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            &&& msg.src == HostId::Controller(controller_id, key)
            &&& msg.content is APIRequest
            &&& msg.dst is APIServer
            &&& s.in_flight().contains(msg)
        } ==> {
            &&& s.ongoing_reconciles(controller_id).contains_key(key)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
        }
    }
}

pub proof fn lemma_true_leads_to_always_every_msg_from_key_is_pending_req_msg_of(self, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef)
    requires
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Self::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))),
        spec.entails(always(lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Self::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)))),
        spec.entails(always(lift_state(Self::no_pending_req_msg_at_reconcile_state(
                controller_id,
                key,
                self.reconcile_model(controller_id).done
            )))),
        spec.entails(always(lift_state(Self::no_pending_req_msg_at_reconcile_state(
                controller_id,
                key,
                self.reconcile_model(controller_id).error
            )))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::every_msg_from_key_is_pending_req_msg_of(controller_id, key))))),
{
    let requirements = |msg: Message, s: ClusterState| {
        ({
            &&& msg.src == HostId::Controller(controller_id, key)
            &&& msg.content is APIRequest
            &&& msg.dst is APIServer
            &&& s.in_flight().contains(msg)
        }) ==> ({
            &&& s.ongoing_reconciles(controller_id).contains_key(key)
            &&& Self::pending_req_msg_is(controller_id, s, key, msg)
        })
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        &&& msg.src == HostId::Controller(controller_id, key)
        &&& msg.content is APIRequest
        &&& msg.dst is APIServer
        &&& s.in_flight().contains(msg)
    };

    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
        &&& Self::crash_disabled(controller_id)(s)
        &&& Self::req_drop_disabled()(s)
        &&& Self::pod_monkey_disabled()(s)
        &&& Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key)(s)
        &&& Self::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
        &&& Self::no_pending_req_msg_at_reconcile_state(
                controller_id,
                key,
                self.reconcile_model(controller_id).done
            )(s)
        &&& Self::no_pending_req_msg_at_reconcile_state(
                controller_id,
                key,
                self.reconcile_model(controller_id).error
            )(s)
    };

    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if requirements_antecedent(msg, s_prime) {
                if s.in_flight().contains(msg) {}

                let next_step = choose |step| self.next_step(s, s_prime, step);
                match next_step {
                    Step::ControllerStep((id, resp_msg_opt, cr_key_opt)) => {
                        let resp_msg = resp_msg_opt.unwrap();
                        let cr_key = cr_key_opt.unwrap();

                        if id == controller_id
                            && cr_key_opt is Some && cr_key == key {
                            // Requires invariant
                            // `pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg`
                            // if there's an incoming message, the `no_pending_req_msg_at_reconcile_state`
                            // family if there's not one (meaning we're done).
                            //
                            // (comment left to provide a hint of the reasoning needed).
                        }
                    },
                    _ => {},
                }
            }
        }
    }

    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id)),
        lift_state(Self::crash_disabled(controller_id)),
        lift_state(Self::req_drop_disabled()),
        lift_state(Self::pod_monkey_disabled()),
        lift_state(Self::pending_req_of_key_is_unique_with_unique_id(controller_id, key)),
        lift_state(Self::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)),
        lift_state(Self::no_pending_req_msg_at_reconcile_state(
            controller_id,
            key,
            self.reconcile_model(controller_id).done
        )),
        lift_state(Self::no_pending_req_msg_at_reconcile_state(
            controller_id,
            key,
            self.reconcile_model(controller_id).error
        ))
    );

    self.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(Self::every_msg_from_key_is_pending_req_msg_of(controller_id, key)),
        lift_state(Self::every_in_flight_req_msg_satisfies(requirements))
    );
}

}
}
