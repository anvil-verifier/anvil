// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, persistent_volume_claim::*, pod::*, resource::*,
    role::*, role_binding::*, secret::*, service::*, service_account::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub proof fn lemma_always_rest_id_counter_is_no_smaller_than<K: ResourceView, R: Reconciler<K>>(
    spec: TempPred<State<K, R>>, rest_id: RestId
)
    requires
        spec.entails(lift_state(rest_id_counter_is(rest_id))),
        spec.entails(always(lift_action(next::<K, R>()))),
    ensures
        spec.entails(always(lift_state(rest_id_counter_is_no_smaller_than::<K, R>(rest_id)))),
{
    let invariant = rest_id_counter_is_no_smaller_than::<K, R>(rest_id);
    init_invariant::<State<K, R>>(spec, rest_id_counter_is(rest_id), next::<K, R>(), invariant);
}

pub open spec fn object_is_well_formed<K: ResourceView, R: Reconciler<K>>(key: ObjectRef) -> StatePred<State<K, R>> {
    |s: State<K, R>| {
        &&& s.resource_obj_of(key).object_ref() == key
        &&& s.resource_obj_of(key).metadata.name.is_Some()
        &&& s.resource_obj_of(key).metadata.namespace.is_Some()
        &&& s.resource_obj_of(key).metadata.resource_version.is_Some()
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

pub open spec fn each_object_in_etcd_is_well_formed<K: ResourceView, R: Reconciler<K>>() -> StatePred<State<K, R>> {
    |s: State<K, R>| {
        forall |key: ObjectRef|
            #[trigger] s.resource_key_exists(key) ==> object_is_well_formed(key)(s)
    }
}

pub proof fn lemma_always_each_object_in_etcd_is_well_formed<K: ResourceView, R: Reconciler<K>>(
    spec: TempPred<State<K, R>>
)
    requires
        spec.entails(lift_state(init::<K, R>())),
        spec.entails(always(lift_action(next::<K, R>()))),
    ensures
        spec.entails(always(lift_state(each_object_in_etcd_is_well_formed::<K, R>()))),
{
    let invariant = each_object_in_etcd_is_well_formed::<K, R>();

    assert forall |s, s_prime: State<K, R>| invariant(s) && #[trigger] next::<K, R>()(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.resource_key_exists(key)
        implies object_is_well_formed(key)(s_prime) by {
            if s.resource_key_exists(key) {} else {}
        }
    }

    init_invariant(spec, init::<K, R>(), next::<K, R>(), invariant);
}

pub open spec fn each_scheduled_key_is_consistent_with_its_object<K: ResourceView, R: Reconciler<K>>() -> StatePred<State<K, R>> {
    |s: State<K, R>| {
        forall |key: ObjectRef|
            #[trigger] s.reconcile_scheduled_for(key)
                ==> s.reconcile_scheduled_obj_of(key).object_ref() == key
    }
}

pub proof fn lemma_always_each_scheduled_key_is_consistent_with_its_object<K: ResourceView, R: Reconciler<K>>(
    spec: TempPred<State<K, R>>
)
    requires
        spec.entails(lift_state(init::<K, R>())),
        spec.entails(always(lift_action(next::<K, R>()))),
    ensures
        spec.entails(always(lift_state(each_scheduled_key_is_consistent_with_its_object::<K, R>()))),
{
    let invariant = each_scheduled_key_is_consistent_with_its_object::<K, R>();

    lemma_always_each_object_in_etcd_is_well_formed::<K, R>(spec);

    let stronger_next = |s, s_prime: State<K, R>| {
        &&& next::<K, R>()(s, s_prime)
        &&& each_object_in_etcd_is_well_formed()(s)
    };

    strengthen_next(spec, next::<K, R>(), each_object_in_etcd_is_well_formed(), stronger_next);

    assert forall |s, s_prime: State<K, R>| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        let step = choose |step| next_step::<K, R>(s, s_prime, step);
        match step {
            Step::ScheduleControllerReconcileStep(input) => {
                assert forall |key: ObjectRef| #[trigger] s_prime.reconcile_scheduled_for(key)
                implies s_prime.reconcile_scheduled_obj_of(key).object_ref() == key by {
                    if input == key {
                        K::from_dynamic_preserves_metadata();
                        K::from_dynamic_preserves_kind();
                        K::object_ref_is_well_formed();
                    } else {
                        assert(s.reconcile_scheduled_for(key));
                    }
                }
            },
            _ => {
                assert forall |key: ObjectRef| #[trigger] s_prime.reconcile_scheduled_for(key)
                implies s_prime.reconcile_scheduled_obj_of(key).object_ref() == key by {
                    assert(s.reconcile_scheduled_for(key));
                }
            }
        }
    }

    init_invariant(spec, init::<K, R>(), stronger_next, invariant);
}

pub open spec fn each_key_in_reconcile_is_consistent_with_its_object<K: ResourceView, R: Reconciler<K>>() -> StatePred<State<K, R>> {
    |s: State<K, R>| {
        forall |key: ObjectRef|
            #[trigger] s.reconcile_state_contains(key)
                ==> s.triggering_cr_of(key).object_ref() == key
    }
}

pub proof fn lemma_always_each_key_in_reconcile_is_consistent_with_its_object<K: ResourceView, R: Reconciler<K>>(
    spec: TempPred<State<K, R>>
)
    requires
        spec.entails(lift_state(init::<K, R>())),
        spec.entails(always(lift_action(next::<K, R>()))),
    ensures
        spec.entails(always(lift_state(each_key_in_reconcile_is_consistent_with_its_object::<K, R>()))),
{
    let invariant = each_key_in_reconcile_is_consistent_with_its_object::<K, R>();

    lemma_always_each_scheduled_key_is_consistent_with_its_object::<K, R>(spec);

    let stronger_next = |s, s_prime: State<K, R>| {
        &&& next::<K, R>()(s, s_prime)
        &&& each_scheduled_key_is_consistent_with_its_object()(s)
    };

    strengthen_next(spec, next::<K, R>(), each_scheduled_key_is_consistent_with_its_object(), stronger_next);

    assert forall |s, s_prime: State<K, R>| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.reconcile_state_contains(key)
        implies s_prime.triggering_cr_of(key).object_ref() == key by {
            if s.reconcile_state_contains(key) {
            } else {
                assert(s.reconcile_scheduled_for(key));
            }
        }
    }

    init_invariant(spec, init::<K, R>(), stronger_next, invariant);
}



}
