use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::{deletion_timestamp, unmarshallable_object, valid_object},
    cluster::*,
    message::*,
};
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn transition_validation_is_reflexive_and_transitive<T: CustomResourceView>() -> bool {
    &&& forall |x: T, y: T|
        (x.spec() == y.spec() && x.status() == y.status()) ==> #[trigger] T::transition_validation(x, y)
    &&& forall |x: T, y: T, z: T| #![trigger T::transition_validation(x, y), T::transition_validation(y, z)]
        T::transition_validation(x, y) && T::transition_validation(y, z) ==> T::transition_validation(x, z)
}

// This spec and also this module are targeted at the relations of the three versions of custom resource object. We know that
// if cr is updated, the old and new object are subject to the transition rule (if any). Since scheduled_cr and triggering_cr
// are derived from the cr in etcd, they are either equal to or satisfy the transition rule with etcd cr.
//
// When the transition rule is transitive, we can determine a linear order of the three custom resource objects.
pub open spec fn transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr<T: CustomResourceView>(controller_id: int, cr: T) -> StatePred<ClusterState> {
    |s| {
        Self::transition_rule_applies_to_etcd_and_scheduled_cr(controller_id, cr)(s)
        && Self::transition_rule_applies_to_scheduled_and_triggering_cr(controller_id, cr)(s)
        && Self::transition_rule_applies_to_etcd_and_triggering_cr(controller_id, cr)(s)
    }
}

pub open spec fn transition_rule_applies_to_etcd_and_scheduled_cr<T: CustomResourceView>(controller_id: int, cr: T) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = cr.object_ref();
        s.scheduled_reconciles(controller_id).contains_key(key)
        && s.resources().contains_key(key)
        && s.resources()[key].metadata.uid.get_Some_0() == s.scheduled_reconciles(controller_id)[key].metadata.uid.get_Some_0()
        ==> T::transition_validation(T::unmarshal(s.resources()[key]).get_Ok_0(), T::unmarshal(s.scheduled_reconciles(controller_id)[key]).get_Ok_0())
    }
}

pub open spec fn transition_rule_applies_to_scheduled_and_triggering_cr<T: CustomResourceView>(controller_id: int, cr: T) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = cr.object_ref();
        s.ongoing_reconciles(controller_id).contains_key(key)
        && s.scheduled_reconciles(controller_id).contains_key(key)
        && s.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.uid.get_Some_0() == s.scheduled_reconciles(controller_id)[key].metadata.uid.get_Some_0()
        ==> T::transition_validation(T::unmarshal(s.scheduled_reconciles(controller_id)[key]).get_Ok_0(), T::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).get_Ok_0())
    }
}

pub open spec fn transition_rule_applies_to_etcd_and_triggering_cr<T: CustomResourceView>(controller_id: int, cr: T) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = cr.object_ref();
        s.ongoing_reconciles(controller_id).contains_key(key)
        && s.resources().contains_key(key)
        && s.resources()[key].metadata.uid.get_Some_0() == s.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.uid.get_Some_0()
        ==> T::transition_validation(T::unmarshal(s.resources()[key]).get_Ok_0(), T::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).get_Ok_0())
    }
}

proof fn lemma_always_transition_rule_applies_to_etcd_and_scheduled_cr<T: CustomResourceView>(self, spec: TempPred<ClusterState>, controller_id: int, cr: T)
    requires
        self.controller_models.contains_key(controller_id),
        self.controller_models[controller_id].reconcile_model.kind == T::kind(),
        self.type_is_installed_in_cluster::<T>(),
        Self::transition_validation_is_reflexive_and_transitive::<T>(),
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::transition_rule_applies_to_etcd_and_scheduled_cr(controller_id, cr)))),
{
    let inv = Self::transition_rule_applies_to_etcd_and_scheduled_cr(controller_id, cr);
    let next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& self.each_custom_object_in_etcd_is_well_formed::<T>()(s)
        &&& self.each_custom_object_in_etcd_is_well_formed::<T>()(s_prime)
        &&& Self::scheduled_cr_has_lower_uid_than_uid_counter(controller_id)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_each_custom_object_in_etcd_is_well_formed::<T>(spec);
    always_to_always_later(spec, lift_state(self.each_custom_object_in_etcd_is_well_formed::<T>()));
    self.lemma_always_scheduled_cr_has_lower_uid_than_uid_counter(spec, controller_id);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(self.next()),
        lift_state(self.each_custom_object_in_etcd_is_well_formed::<T>()),
        later(lift_state(self.each_custom_object_in_etcd_is_well_formed::<T>())),
        lift_state(Self::scheduled_cr_has_lower_uid_than_uid_counter(controller_id)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    let key = cr.object_ref();
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.scheduled_reconciles(controller_id).contains_key(key)
        && s_prime.resources().contains_key(key)
        && s_prime.resources()[key].metadata.uid.get_Some_0() == s_prime.scheduled_reconciles(controller_id)[key].metadata.uid.get_Some_0() {
            let step = choose |step| self.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    T::object_ref_is_well_formed();
                    T::unmarshal_result_determined_by_unmarshal_spec_and_status();
                    T::kind_is_custom_resource();
                    assert(s.scheduled_reconciles(controller_id).contains_key(key) && s.scheduled_reconciles(controller_id)[key] == s_prime.scheduled_reconciles(controller_id)[key]);
                    if !s.resources().contains_key(key) {
                        assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
                        assert(s_prime.resources()[key].metadata.uid.get_Some_0() != s_prime.scheduled_reconciles(controller_id)[key].metadata.uid.get_Some_0());
                    } else if s.resources()[key] != s_prime.resources()[key] {
                        if input.get_Some_0().content.is_delete_request() {
                            assert(T::unmarshal(s_prime.resources()[key]).get_Ok_0().transition_validation(T::unmarshal(s.resources()[key]).get_Ok_0()));
                        } else if input.get_Some_0().content.is_update_request() {
                            assert(T::unmarshal(input.get_Some_0().content.get_update_request().obj).is_Ok());
                            assert(T::unmarshal(s_prime.resources()[key]).get_Ok_0().transition_validation(T::unmarshal(s.resources()[key]).get_Ok_0()));
                        } else {
                            assert(input.get_Some_0().content.is_update_status_request());
                            assert(T::unmarshal(input.get_Some_0().content.get_update_status_request().obj).is_Ok());
                            assert(T::unmarshal(s_prime.resources()[key]).get_Ok_0().transition_validation(T::unmarshal(s.resources()[key]).get_Ok_0()));
                        }
                    }
                },
                Step::ScheduleControllerReconcileStep(input) => {
                    assert(s.resources().contains_key(key) && s.resources()[key] == s_prime.resources()[key]);
                    if !s.scheduled_reconciles(controller_id).contains_key(key) || s.scheduled_reconciles(controller_id)[key] != s_prime.scheduled_reconciles(controller_id)[key] {
                        assert(T::unmarshal(s_prime.scheduled_reconciles(controller_id)[key]).get_Ok_0() == T::unmarshal(s_prime.resources()[key]).get_Ok_0());
                    }
                },
                _ => {}
            }
        }
    }
    init_invariant(spec, self.init(), next, inv);
}

proof fn lemma_always_triggering_cr_is_in_correct_order<T: CustomResourceView>(self, spec: TempPred<ClusterState>, controller_id: int, cr: T)
    requires
        self.controller_models.contains_key(controller_id),
        self.controller_models[controller_id].reconcile_model.kind == T::kind(),
        self.type_is_installed_in_cluster::<T>(),
        Self::transition_validation_is_reflexive_and_transitive::<T>(),
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures
        spec.entails(always(lift_state(Self::transition_rule_applies_to_etcd_and_triggering_cr(controller_id, cr)))),
        spec.entails(always(lift_state(Self::transition_rule_applies_to_scheduled_and_triggering_cr(controller_id, cr)))),
{
    let inv = |s| {
        &&& Self::transition_rule_applies_to_etcd_and_triggering_cr(controller_id, cr)(s)
        &&& Self::transition_rule_applies_to_scheduled_and_triggering_cr(controller_id, cr)(s)
    };
    let next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& self.each_custom_object_in_etcd_is_well_formed::<T>()(s)
        &&& self.each_custom_object_in_etcd_is_well_formed::<T>()(s_prime)
        &&& Self::triggering_cr_has_lower_uid_than_uid_counter(controller_id)(s)
        &&& Self::transition_rule_applies_to_etcd_and_scheduled_cr(controller_id, cr)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_each_custom_object_in_etcd_is_well_formed::<T>(spec);
    always_to_always_later(spec, lift_state(self.each_custom_object_in_etcd_is_well_formed::<T>()));
    self.lemma_always_triggering_cr_has_lower_uid_than_uid_counter(spec, controller_id);
    self.lemma_always_transition_rule_applies_to_etcd_and_scheduled_cr(spec, controller_id, cr);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(self.next()),
        lift_state(self.each_custom_object_in_etcd_is_well_formed::<T>()),
        later(lift_state(self.each_custom_object_in_etcd_is_well_formed::<T>())),
        lift_state(Self::triggering_cr_has_lower_uid_than_uid_counter(controller_id)),
        lift_state(Self::transition_rule_applies_to_etcd_and_scheduled_cr(controller_id, cr)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = cr.object_ref();
        let step = choose |step| self.next_step(s, s_prime, step);
        if s_prime.ongoing_reconciles(controller_id).contains_key(key)
        && s_prime.resources().contains_key(key)
        && s_prime.resources()[key].metadata.uid.get_Some_0() == s_prime.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.uid.get_Some_0() {
            match step {
                Step::APIServerStep(input) => {
                    T::object_ref_is_well_formed();
                    T::marshal_preserves_metadata();
                    T::unmarshal_result_determined_by_unmarshal_spec_and_status();
                    T::kind_is_custom_resource();
                    assert(s.ongoing_reconciles(controller_id).contains_key(key) && s.ongoing_reconciles(controller_id)[key].triggering_cr == s_prime.ongoing_reconciles(controller_id)[key].triggering_cr);
                    if !s.resources().contains_key(key) {
                        assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
                        assert(s_prime.resources()[key].metadata.uid.get_Some_0() != s_prime.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.uid.get_Some_0());
                    } else if s.resources()[key] != s_prime.resources()[key] {
                        if input.get_Some_0().content.is_delete_request() {
                            assert(s_prime.resources()[key].spec == s.resources()[key].spec);
                            assert(T::unmarshal(s_prime.resources()[key]).get_Ok_0().transition_validation(T::unmarshal(s.resources()[key]).get_Ok_0()));
                        } else if input.get_Some_0().content.is_update_request() {
                            assert(T::unmarshal(input.get_Some_0().content.get_update_request().obj).is_Ok());
                            assert(T::unmarshal(s_prime.resources()[key]).get_Ok_0().transition_validation(T::unmarshal(s.resources()[key]).get_Ok_0()));
                        } else {
                            assert(input.get_Some_0().content.is_update_status_request());
                            assert(T::unmarshal(input.get_Some_0().content.get_update_status_request().obj).is_Ok());
                            assert(T::unmarshal(s_prime.resources()[key]).get_Ok_0().transition_validation(T::unmarshal(s.resources()[key]).get_Ok_0()));
                        }
                    }
                },
                Step::ControllerStep(_) => {
                    assert(s.resources().contains_key(key) && s.resources()[key] == s_prime.resources()[key]);
                    if !s.ongoing_reconciles(controller_id).contains_key(key) || s.ongoing_reconciles(controller_id)[key].triggering_cr != s_prime.ongoing_reconciles(controller_id)[key].triggering_cr {
                        assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
                    }
                },
                _ => {}
            }
        }
        if s_prime.ongoing_reconciles(controller_id).contains_key(key)
        && s_prime.scheduled_reconciles(controller_id).contains_key(key)
        && s_prime.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.uid.get_Some_0() == s_prime.scheduled_reconciles(controller_id)[key].metadata.uid.get_Some_0() {
            match step {
                Step::ScheduleControllerReconcileStep(_) => {
                    if !s.scheduled_reconciles(controller_id).contains_key(key) || s.scheduled_reconciles(controller_id)[key] != s_prime.scheduled_reconciles(controller_id)[key] {
                        assert(T::unmarshal(s_prime.scheduled_reconciles(controller_id)[key]).get_Ok_0().transition_validation(T::unmarshal(s.resources()[key]).get_Ok_0()));
                        assert(T::unmarshal(s.resources()[key]).get_Ok_0().transition_validation(T::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).get_Ok_0()));
                    }
                    assert(Self::transition_rule_applies_to_scheduled_and_triggering_cr(controller_id, cr)(s_prime));
                },
                _ => {
                    assert(Self::transition_rule_applies_to_scheduled_and_triggering_cr(controller_id, cr)(s_prime));
                }
            }
        }
    }
    init_invariant(spec, self.init(), next, inv);
    always_weaken(spec, lift_state(inv), lift_state(Self::transition_rule_applies_to_etcd_and_triggering_cr(controller_id, cr)));
    always_weaken(spec, lift_state(inv), lift_state(Self::transition_rule_applies_to_scheduled_and_triggering_cr(controller_id, cr)));
}


pub proof fn lemma_always_transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr<T: CustomResourceView>(self, spec: TempPred<ClusterState>, controller_id: int, cr: T)
    requires
        self.controller_models.contains_key(controller_id),
        self.controller_models[controller_id].reconcile_model.kind == T::kind(),
        self.type_is_installed_in_cluster::<T>(),
        Self::transition_validation_is_reflexive_and_transitive::<T>(),
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(controller_id, cr)))),
{
    self.lemma_always_transition_rule_applies_to_etcd_and_scheduled_cr(spec, controller_id, cr);
    self.lemma_always_triggering_cr_is_in_correct_order(spec, controller_id, cr);
    combine_spec_entails_always_n!(
        spec,
        lift_state(Self::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(controller_id, cr)),
        lift_state(Self::transition_rule_applies_to_etcd_and_scheduled_cr(controller_id, cr)),
        lift_state(Self::transition_rule_applies_to_scheduled_and_triggering_cr(controller_id, cr)),
        lift_state(Self::transition_rule_applies_to_etcd_and_triggering_cr(controller_id, cr))
    );
}

}

}
