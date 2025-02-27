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

// TODO: Investigate flaky proof.
#[verifier(rlimit(4000))]
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

pub open spec fn cr_objects_in_etcd_satisfy_state_validation<T: CustomResourceView>() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            let unmarshal_result = 
                T::unmarshal(s.resources()[key]);
            #[trigger] s.resources().contains_key(key)
            && key.kind.is_CustomResourceKind()
            && key.kind == T::kind()
            ==> unmarshal_result.is_Ok()
                && unmarshal_result.unwrap().state_validation()
        }
    }
}

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
            && key.kind.is_CustomResourceKind()
            && key.kind == T::kind()
            ==> unmarshal_result.is_Ok()
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

    let inv_matrix = |key: ObjectRef| |s: ClusterState| {
        let unmarshal_result = 
                T::unmarshal(s.scheduled_reconciles(controller_id)[key]);
        s.scheduled_reconciles(controller_id).contains_key(key)
        && key.kind.is_CustomResourceKind()
        && key.kind == T::kind()
        ==> unmarshal_result.is_Ok()
            && unmarshal_result.unwrap().state_validation()
    };
    let inv_antecedent = |key: ObjectRef| |s: ClusterState| {
        s.scheduled_reconciles(controller_id).contains_key(key)
        && key.kind.is_CustomResourceKind()
        && key.kind == T::kind()
    };

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
            && key.kind.is_CustomResourceKind()
            && key.kind == T::kind()
            ==> unmarshal_result.is_Ok()
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

    let inv_matrix = |key: ObjectRef| |s: ClusterState| {
        let unmarshal_result = 
                T::unmarshal(s.scheduled_reconciles(controller_id)[key]);
        s.scheduled_reconciles(controller_id).contains_key(key)
        && key.kind.is_CustomResourceKind()
        && key.kind == T::kind()
        ==> unmarshal_result.is_Ok()
            && unmarshal_result.unwrap().state_validation()
    };
    let inv_antecedent = |key: ObjectRef| |s: ClusterState| {
        s.scheduled_reconciles(controller_id).contains_key(key)
        && key.kind.is_CustomResourceKind()
        && key.kind == T::kind()
    };

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

}

}
