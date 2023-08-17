// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, object_meta::*, persistent_volume_claim::*, pod::*,
    resource::*, role::*, role_binding::*, secret::*, service::*, service_account::*,
    stateful_set::*,
};
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

pub open spec fn metadata_is_well_formed(metadata: ObjectMetaView) -> bool {
    &&& metadata.name.is_Some()
    &&& metadata.namespace.is_Some()
    &&& metadata.resource_version.is_Some()
    &&& metadata.uid.is_Some()
}

pub open spec fn etcd_object_is_well_formed(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        &&& s.resource_obj_of(key).object_ref() == key
        &&& Self::metadata_is_well_formed(s.resource_obj_of(key).metadata)
        &&& {
            &&& key.kind == ConfigMapView::kind() ==> ConfigMapView::from_dynamic_object(s.resource_obj_of(key)).is_Ok()
            &&& key.kind == PersistentVolumeClaimView::kind() ==> PersistentVolumeClaimView::from_dynamic_object(s.resource_obj_of(key)).is_Ok()
            &&& key.kind == PodView::kind() ==> PodView::from_dynamic_object(s.resource_obj_of(key)).is_Ok()
            &&& key.kind == RoleBindingView::kind() ==> RoleBindingView::from_dynamic_object(s.resource_obj_of(key)).is_Ok()
            &&& key.kind == RoleView::kind() ==> RoleView::from_dynamic_object(s.resource_obj_of(key)).is_Ok()
            &&& key.kind == SecretView::kind() ==> SecretView::from_dynamic_object(s.resource_obj_of(key)).is_Ok()
            &&& key.kind == ServiceView::kind() ==> ServiceView::from_dynamic_object(s.resource_obj_of(key)).is_Ok()
            &&& key.kind == StatefulSetView::kind() ==> StatefulSetView::from_dynamic_object(s.resource_obj_of(key)).is_Ok()
        }
    }
}

pub open spec fn each_object_in_etcd_is_well_formed() -> StatePred<Self> {
    |s: Self| {
        forall |key: ObjectRef|
            #[trigger] s.resource_key_exists(key)
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
        assert forall |key: ObjectRef| #[trigger] s_prime.resource_key_exists(key)
        implies Self::etcd_object_is_well_formed(key)(s_prime) by {
            if s.resource_key_exists(key) {} else {}
        }
    }

    init_invariant(spec, Self::init(), Self::next(), invariant);
}

pub open spec fn each_scheduled_object_has_consistent_key_and_valid_metadata() -> StatePred<Self> {
    |s: Self| {
        forall |key: ObjectRef|
            #[trigger] s.reconcile_scheduled_for(key)
                ==> s.reconcile_scheduled_obj_of(key).object_ref() == key
                    && Self::metadata_is_well_formed(s.reconcile_scheduled_obj_of(key).metadata())
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
        assert forall |key: ObjectRef| #[trigger] s_prime.reconcile_scheduled_for(key)
        implies s_prime.reconcile_scheduled_obj_of(key).object_ref() == key
        && Self::metadata_is_well_formed(s_prime.reconcile_scheduled_obj_of(key).metadata()) by {
            let step = choose |step| Self::next_step(s, s_prime, step);
            match step {
                Step::ScheduleControllerReconcileStep(input) => {

                        if input == key {
                            K::from_dynamic_preserves_metadata();
                            K::from_dynamic_preserves_kind();
                            K::object_ref_is_well_formed();
                        } else {
                            assert(s.reconcile_scheduled_for(key));
                        }
                },
                _ => {
                        assert(s.reconcile_scheduled_for(key));
                }
            }
        }
    }

    init_invariant(spec, Self::init(), stronger_next, invariant);
}

pub open spec fn each_object_in_reconcile_has_consistent_key_and_valid_metadata() -> StatePred<Self> {
    |s: Self| {
        forall |key: ObjectRef|
            #[trigger] s.reconcile_state_contains(key)
                ==> s.triggering_cr_of(key).object_ref() == key
                    && Self::metadata_is_well_formed(s.triggering_cr_of(key).metadata())
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
        assert forall |key: ObjectRef| #[trigger] s_prime.reconcile_state_contains(key)
        implies s_prime.triggering_cr_of(key).object_ref() == key
        && Self::metadata_is_well_formed(s_prime.triggering_cr_of(key).metadata()) by {
            if s.reconcile_state_contains(key) {
            } else {
                assert(s.reconcile_scheduled_for(key));
            }
        }
    }

    init_invariant(spec, Self::init(), stronger_next, invariant);
}

}

}
