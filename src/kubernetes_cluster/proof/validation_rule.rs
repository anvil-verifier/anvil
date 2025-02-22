// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn marshal_preserves_spec() -> bool {
    forall |d: DynamicObjectView|
        #[trigger] K::unmarshal(d).is_Ok()
            ==> K::unmarshal_spec(d.spec).get_Ok_0() == K::unmarshal(d).get_Ok_0().spec()
}

pub open spec fn marshal_preserves_status() -> bool {
    forall |d: DynamicObjectView|
        #[trigger] K::unmarshal(d).is_Ok()
            ==> K::unmarshal_status(d.status).get_Ok_0() == K::unmarshal(d).get_Ok_0().status()
}

// The relexitivity allows the metadata to be different.
pub open spec fn transition_validation_is_reflexive_and_transitive() -> bool {
    &&& forall |x: K, y: K|  (x.spec() == y.spec() && x.status() == y.status()) ==> #[trigger] K::transition_validation(x, y)
    &&& forall |x: K, y: K, z: K| #![trigger K::transition_validation(x, y), K::transition_validation(y, z)]
        K::transition_validation(x, y) && K::transition_validation(y, z) ==> K::transition_validation(x, z)
}

// This spec and also this module are targeted at the relations of the three versions of custom resource object. We know that
// if cr is updated, the old and new object are subject to the transition rule (if any). Since scheduled_cr and triggering_cr
// are derived from the cr in etcd, they are either equal to or satisfy the transition rule with etcd cr.
//
// When the transition rule is transitive, we can determine a linear order of the three custom resource objects.
pub open spec fn transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(cr: K) -> StatePred<Self> {
    |s: Self| {
        Self::transition_rule_applies_to_etcd_and_scheduled_cr(cr)(s)
        && Self::transition_rule_applies_to_scheduled_and_triggering_cr(cr)(s)
        && Self::transition_rule_applies_to_etcd_and_triggering_cr(cr)(s)
    }
}

pub proof fn lemma_always_transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(spec: TempPred<Self>, cr: K)
    requires
        K::kind().is_CustomResourceKind(),
        Self::marshal_preserves_spec(),
        Self::marshal_preserves_status(),
        Self::transition_validation_is_reflexive_and_transitive(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(cr)))),
{
    Self::lemma_always_transition_rule_applies_to_etcd_and_scheduled_cr(spec, cr);
    Self::lemma_always_triggering_cr_is_in_correct_order(spec, cr);
    combine_spec_entails_always_n!(
        spec, lift_state(Self::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(cr)),
        lift_state(Self::transition_rule_applies_to_etcd_and_scheduled_cr(cr)),
        lift_state(Self::transition_rule_applies_to_scheduled_and_triggering_cr(cr)),
        lift_state(Self::transition_rule_applies_to_etcd_and_triggering_cr(cr))
    );
}

pub open spec fn transition_rule_applies_to_etcd_and_scheduled_cr(cr: K) -> StatePred<Self> {
    |s: Self| {
        let key = cr.object_ref();
        s.scheduled_reconciles().contains_key(key)
        && s.resources().contains_key(key)
        && s.resources()[key].metadata.uid.get_Some_0() == s.scheduled_reconciles()[key].metadata().uid.get_Some_0()
        ==> K::transition_validation(K::unmarshal(s.resources()[key]).get_Ok_0(), s.scheduled_reconciles()[key])
    }
}

proof fn lemma_always_transition_rule_applies_to_etcd_and_scheduled_cr(spec: TempPred<Self>, cr: K)
    requires
        K::kind().is_CustomResourceKind(),
        Self::transition_validation_is_reflexive_and_transitive(),
        Self::marshal_preserves_spec(),
        Self::marshal_preserves_status(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures spec.entails(always(lift_state(Self::transition_rule_applies_to_etcd_and_scheduled_cr(cr)))),
{
    let inv = Self::transition_rule_applies_to_etcd_and_scheduled_cr(cr);
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
        &&& Self::each_object_in_etcd_is_well_formed()(s_prime)
        &&& Self::scheduled_cr_has_lower_uid_than_uid_counter()(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(Self::each_object_in_etcd_is_well_formed()));
    Self::lemma_always_scheduled_cr_has_lower_uid_than_uid_counter(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()), lift_state(Self::each_object_in_etcd_is_well_formed()),
        later(lift_state(Self::each_object_in_etcd_is_well_formed())), lift_state(Self::scheduled_cr_has_lower_uid_than_uid_counter())
    );
    let key = cr.object_ref();
    K::object_ref_is_well_formed();
    K::unmarshal_result_determined_by_unmarshal_spec_and_status();
    assert forall |s, s_prime: Self| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.scheduled_reconciles().contains_key(key) && s_prime.resources().contains_key(key)
        && s_prime.resources()[key].metadata.uid.get_Some_0() == s_prime.scheduled_reconciles()[key].metadata().uid.get_Some_0() {
            let step = choose |step: Step<MsgType<E>>| Self::next_step(s, s_prime, step);
            match step {
                Step::ApiServerStep(input) => {
//                    assert(s.scheduled_reconciles().contains_key(key) && s.scheduled_reconciles()[key] == s_prime.scheduled_reconciles()[key]);
                    if !s.resources().contains_key(key) {
//                        assert(s_prime.resources()[key].metadata.uid == Some(s.kubernetes_api_state.uid_counter));
//                        assert(s_prime.resources()[key].metadata.uid.get_Some_0() != s_prime.scheduled_reconciles()[key].metadata().uid.get_Some_0());
                    } else if s.resources()[key] != s_prime.resources()[key] {
                        if input.get_Some_0().content.is_delete_request() {
//                            assert(s_prime.resources()[key].spec == s.resources()[key].spec);
                            assert(K::transition_validation(
                                K::unmarshal(s_prime.resources()[key]).get_Ok_0(),
                                K::unmarshal(s.resources()[key]).get_Ok_0()
                            ));
                        } else if input.get_Some_0().content.is_update_request() {
//                            assert(K::unmarshal(input.get_Some_0().content.get_update_request().obj).is_Ok());
//                            assert(K::transition_validation(
//                                K::unmarshal(s_prime.resources()[key]).get_Ok_0(),
//                                K::unmarshal(s.resources()[key]).get_Ok_0()
//                            ));
                        } else {
//                            assert(input.get_Some_0().content.is_update_status_request());
//                            assert(K::unmarshal(input.get_Some_0().content.get_update_status_request().obj).is_Ok());
//                            assert(K::transition_validation(
//                                K::unmarshal(s_prime.resources()[key]).get_Ok_0(),
//                                K::unmarshal(s.resources()[key]).get_Ok_0()
//                            ));
                        }
                    }
                },
                Step::ScheduleControllerReconcileStep(input) => {
//                    assert(s.resources().contains_key(key) && s.resources()[key] == s_prime.resources()[key]);
                    if !s.scheduled_reconciles().contains_key(key) || s.scheduled_reconciles()[key] != s_prime.scheduled_reconciles()[key] {
//                        assert(s_prime.scheduled_reconciles()[key] == K::unmarshal(s_prime.resources()[key]).get_Ok_0());
                    }
                },
                _ => {}
            }
        }
    }
    init_invariant(spec, Self::init(), next, inv);
}

pub open spec fn transition_rule_applies_to_etcd_and_triggering_cr(cr: K) -> StatePred<Self> {
    |s: Self| {
        let key = cr.object_ref();
        s.ongoing_reconciles().contains_key(key)
        && s.resources().contains_key(key)
        && s.resources()[key].metadata.uid.get_Some_0() == s.ongoing_reconciles()[key].triggering_cr.metadata().uid.get_Some_0()
        ==> K::transition_validation(K::unmarshal(s.resources()[key]).get_Ok_0(), s.ongoing_reconciles()[key].triggering_cr)
    }
}

pub open spec fn transition_rule_applies_to_scheduled_and_triggering_cr(cr: K) -> StatePred<Self> {
    |s: Self| {
        let key = cr.object_ref();
        s.ongoing_reconciles().contains_key(key)
        && s.scheduled_reconciles().contains_key(key)
        && s.ongoing_reconciles()[key].triggering_cr.metadata().uid.get_Some_0() == s.scheduled_reconciles()[key].metadata().uid.get_Some_0()
        ==> K::transition_validation(s.scheduled_reconciles()[key], s.ongoing_reconciles()[key].triggering_cr)
    }
}

proof fn lemma_always_triggering_cr_is_in_correct_order(spec: TempPred<Self>, cr: K)
    requires
        K::kind().is_CustomResourceKind(),
        Self::marshal_preserves_spec(),
        Self::marshal_preserves_status(),
        Self::transition_validation_is_reflexive_and_transitive(),
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::transition_rule_applies_to_etcd_and_triggering_cr(cr)))),
        spec.entails(always(lift_state(Self::transition_rule_applies_to_scheduled_and_triggering_cr(cr)))),
{
    let inv = |s: Self| {
        &&& Self::transition_rule_applies_to_etcd_and_triggering_cr(cr)(s)
        &&& Self::transition_rule_applies_to_scheduled_and_triggering_cr(cr)(s)
    };
    let next = |s, s_prime| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
        &&& Self::each_object_in_etcd_is_well_formed()(s_prime)
        &&& Self::triggering_cr_has_lower_uid_than_uid_counter()(s)
        &&& Self::transition_rule_applies_to_etcd_and_scheduled_cr(cr)(s)
    };
    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(Self::each_object_in_etcd_is_well_formed()));
    Self::lemma_always_triggering_cr_has_lower_uid_than_uid_counter(spec);
    Self::lemma_always_transition_rule_applies_to_etcd_and_scheduled_cr(spec, cr);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(Self::next()),
        lift_state(Self::each_object_in_etcd_is_well_formed()),
        later(lift_state(Self::each_object_in_etcd_is_well_formed())),
        lift_state(Self::triggering_cr_has_lower_uid_than_uid_counter()),
        lift_state(Self::transition_rule_applies_to_etcd_and_scheduled_cr(cr))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = cr.object_ref();
        K::object_ref_is_well_formed();
        K::marshal_preserves_metadata();
        K::unmarshal_result_determined_by_unmarshal_spec_and_status();
        let step = choose |step| Self::next_step(s, s_prime, step);
        if s_prime.ongoing_reconciles().contains_key(key) && s_prime.resources().contains_key(key)
        && s_prime.resources()[key].metadata.uid.get_Some_0() == s_prime.ongoing_reconciles()[key].triggering_cr.metadata().uid.get_Some_0() {
            match step {
                Step::ApiServerStep(input) => {
//                    assert(s.ongoing_reconciles().contains_key(key) && s.ongoing_reconciles()[key].triggering_cr == s_prime.ongoing_reconciles()[key].triggering_cr);
                    if !s.resources().contains_key(key) {
//                        assert(s_prime.resources()[key].metadata.uid == Some(s.kubernetes_api_state.uid_counter));
//                        assert(s_prime.resources()[key].metadata.uid.get_Some_0() != s_prime.ongoing_reconciles()[key].triggering_cr.metadata().uid.get_Some_0());
                    } else if s.resources()[key] != s_prime.resources()[key] {
                        if input.get_Some_0().content.is_delete_request() {
//                            assert(s_prime.resources()[key].spec == s.resources()[key].spec);
                            assert(K::transition_validation(
                                K::unmarshal(s_prime.resources()[key]).get_Ok_0(),
                                K::unmarshal(s.resources()[key]).get_Ok_0()
                            ));
                        } else if input.get_Some_0().content.is_update_request() {
//                            assert(K::unmarshal(input.get_Some_0().content.get_update_request().obj).is_Ok());
//                            assert(K::transition_validation(
//                                K::unmarshal(s_prime.resources()[key]).get_Ok_0(),
//                                K::unmarshal(s.resources()[key]).get_Ok_0()
//                            ));
                        } else {
//                            assert(input.get_Some_0().content.is_update_status_request());
//                            assert(K::unmarshal(input.get_Some_0().content.get_update_status_request().obj).is_Ok());
//                            assert(K::transition_validation(
//                                K::unmarshal(s_prime.resources()[key]).get_Ok_0(),
//                                K::unmarshal(s.resources()[key]).get_Ok_0()
//                            ));
                        }
                    }
                },
                Step::ControllerStep(_) => {
//                    assert(s.resources().contains_key(key) && s.resources()[key] == s_prime.resources()[key]);
                    if !s.ongoing_reconciles().contains_key(key) || s.ongoing_reconciles()[key].triggering_cr != s_prime.ongoing_reconciles()[key].triggering_cr {
//                        assert(s_prime.ongoing_reconciles()[key].triggering_cr == s.scheduled_reconciles()[key]);
                    }
                },
                _ => {}
            }
        }
        if s_prime.ongoing_reconciles().contains_key(key) && s_prime.scheduled_reconciles().contains_key(key)
        && s_prime.ongoing_reconciles()[key].triggering_cr.metadata().uid.get_Some_0() == s_prime.scheduled_reconciles()[key].metadata().uid.get_Some_0() {
            match step {
                Step::ScheduleControllerReconcileStep(_) => {
                    if !s.scheduled_reconciles().contains_key(key) || s.scheduled_reconciles()[key] != s_prime.scheduled_reconciles()[key] {
//                        assert(K::transition_validation(s_prime.scheduled_reconciles()[key], K::unmarshal(s.resources()[key]).get_Ok_0()));
//                        assert(K::transition_validation(K::unmarshal(s.resources()[key]).get_Ok_0(), s.ongoing_reconciles()[key].triggering_cr));
                    }
//                    assert(Self::transition_rule_applies_to_scheduled_and_triggering_cr(cr)(s_prime));
                },
                _ => {
//                    assert(Self::transition_rule_applies_to_scheduled_and_triggering_cr(cr)(s_prime));
                }
            }
        }
    }
    init_invariant(spec, Self::init(), next, inv);
    always_weaken(spec, lift_state(inv), lift_state(Self::transition_rule_applies_to_etcd_and_triggering_cr(cr)));
    always_weaken(spec, lift_state(inv), lift_state(Self::transition_rule_applies_to_scheduled_and_triggering_cr(cr)));
}

}

}
