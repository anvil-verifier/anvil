// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, cluster_state_machine::Step, message::*};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub proof fn lemma_always_has_rest_id_counter_no_smaller_than(
    spec: TempPred<Self>, rest_id: RestId
)
    requires
        spec.entails(lift_state(Self::rest_id_counter_is(rest_id))),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::rest_id_counter_is_no_smaller_than(rest_id)))),
{
    let invariant = Self::rest_id_counter_is_no_smaller_than(rest_id);
    init_invariant::<Self>(spec, Self::rest_id_counter_is(rest_id), Self::next(), invariant);
}

pub open spec fn etcd_object_is_well_formed(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        &&& s.resources()[key].object_ref() == key
        &&& s.resources()[key].metadata.well_formed()
        &&& s.resources()[key].metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
        &&& {
            &&& key.kind == ConfigMapView::kind() ==> ConfigMapView::unmarshal(s.resources()[key]).is_Ok()
            &&& key.kind == DaemonSetView::kind() ==> DaemonSetView::unmarshal(s.resources()[key]).is_Ok()
            &&& key.kind == PersistentVolumeClaimView::kind() ==> PersistentVolumeClaimView::unmarshal(s.resources()[key]).is_Ok()
            &&& key.kind == PodView::kind() ==> PodView::unmarshal(s.resources()[key]).is_Ok()
            &&& key.kind == RoleBindingView::kind() ==> RoleBindingView::unmarshal(s.resources()[key]).is_Ok()
            &&& key.kind == RoleView::kind() ==> RoleView::unmarshal(s.resources()[key]).is_Ok()
            &&& key.kind == SecretView::kind() ==> SecretView::unmarshal(s.resources()[key]).is_Ok()
            &&& key.kind == ServiceView::kind() ==> ServiceView::unmarshal(s.resources()[key]).is_Ok()
            &&& key.kind == StatefulSetView::kind() ==> StatefulSetView::unmarshal(s.resources()[key]).is_Ok()
            &&& key.kind == K::kind() ==> K::unmarshal(s.resources()[key]).is_Ok()
        }
    }
}

pub open spec fn each_object_in_etcd_is_well_formed() -> StatePred<Self> {
    |s: Self| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
                ==> Self::etcd_object_is_well_formed(key)(s)
    }
}

pub proof fn lemma_always_each_object_in_etcd_is_well_formed(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::each_object_in_etcd_is_well_formed()))),
{
    let invariant = Self::each_object_in_etcd_is_well_formed();

    assert forall |s, s_prime: Self| invariant(s) && #[trigger] Self::next()(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key)
        implies Self::etcd_object_is_well_formed(key)(s_prime) by {
            K::unmarshal_result_determined_by_unmarshal_spec();
            if s.resources().contains_key(key) {} else {}
        }
    }

    init_invariant(spec, Self::init(), Self::next(), invariant);
}

pub open spec fn each_scheduled_object_has_consistent_key_and_valid_metadata() -> StatePred<Self> {
    |s: Self| {
        forall |key: ObjectRef|
            #[trigger] s.scheduled_reconciles().contains_key(key)
                ==> s.scheduled_reconciles()[key].object_ref() == key
                    && s.scheduled_reconciles()[key].metadata().well_formed()
    }
}

pub proof fn lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(
    spec: TempPred<Self>
)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::each_scheduled_object_has_consistent_key_and_valid_metadata()))),
{
    let invariant = Self::each_scheduled_object_has_consistent_key_and_valid_metadata();

    Self::lemma_always_each_object_in_etcd_is_well_formed(spec);

    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
    };

    strengthen_next(spec, Self::next(), Self::each_object_in_etcd_is_well_formed(), stronger_next);

    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles().contains_key(key)
        implies s_prime.scheduled_reconciles()[key].object_ref() == key
        && s_prime.scheduled_reconciles()[key].metadata().well_formed() by {
            let step = choose |step| Self::next_step(s, s_prime, step);
            match step {
                Step::ScheduleControllerReconcileStep(input) => {

                        if input == key {
                            K::marshal_preserves_metadata();
                            K::marshal_preserves_kind();
                            K::object_ref_is_well_formed();
                        } else {
                            assert(s.scheduled_reconciles().contains_key(key));
                        }
                },
                _ => {
                        assert(s.scheduled_reconciles().contains_key(key));
                }
            }
        }
    }

    init_invariant(spec, Self::init(), stronger_next, invariant);
}

pub open spec fn each_object_in_reconcile_has_consistent_key_and_valid_metadata() -> StatePred<Self> {
    |s: Self| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles().contains_key(key)
                ==> s.ongoing_reconciles()[key].triggering_cr.object_ref() == key
                    && s.ongoing_reconciles()[key].triggering_cr.metadata().well_formed()
    }
}

pub proof fn lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(
    spec: TempPred<Self>
)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
{
    let invariant = Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata();

    Self::lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec);

    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::each_scheduled_object_has_consistent_key_and_valid_metadata()(s)
    };

    strengthen_next(spec, Self::next(), Self::each_scheduled_object_has_consistent_key_and_valid_metadata(), stronger_next);

    assert forall |s, s_prime: Self| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles().contains_key(key)
        implies s_prime.ongoing_reconciles()[key].triggering_cr.object_ref() == key
        && s_prime.ongoing_reconciles()[key].triggering_cr.metadata().well_formed() by {
            if s.ongoing_reconciles().contains_key(key) {
            } else {
                assert(s.scheduled_reconciles().contains_key(key));
            }
        }
    }

    init_invariant(spec, Self::init(), stronger_next, invariant);
}

}

}
