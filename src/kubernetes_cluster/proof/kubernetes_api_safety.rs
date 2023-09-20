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

pub open spec fn has_lower_uid_than(obj: DynamicObjectView, uid: Uid) -> bool {
    obj.metadata.uid.is_Some() && obj.metadata.uid.get_Some_0() < uid
}

pub open spec fn every_object_in_etcd_has_lower_uid_than_uid_counter() -> StatePred<Self> {
    |s: Self| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key) ==> Self::has_lower_uid_than(s.resources()[key], s.kubernetes_api_state.uid_counter)
    }
}

pub proof fn lemma_always_every_object_in_etcd_has_lower_uid_than_uid_counter(spec: TempPred<Self>)
    requires
        spec.entails(lift_state(Self::init())),
        spec.entails(always(lift_action(Self::next()))),
    ensures
        spec.entails(always(lift_state(Self::every_object_in_etcd_has_lower_uid_than_uid_counter()))),
{
    let invariant = Self::every_object_in_etcd_has_lower_uid_than_uid_counter();
    assert forall |s, s_prime| invariant(s) && #[trigger] Self::next()(s, s_prime) implies invariant(s_prime) by {
        assert forall |key| #[trigger] s_prime.resources().contains_key(key) implies Self::has_lower_uid_than(s_prime.resources()[key], s_prime.kubernetes_api_state.uid_counter) by {
            assert(s_prime.kubernetes_api_state.uid_counter >= s.kubernetes_api_state.uid_counter);
            if s.resources().contains_key(key) {
                assert(Self::has_lower_uid_than(s.resources()[key], s.kubernetes_api_state.uid_counter));
                assert(s.resources()[key].metadata.uid == s_prime.resources()[key].metadata.uid);
            } else {
                assert(Self::has_lower_uid_than(s_prime.resources()[key], s_prime.kubernetes_api_state.uid_counter));
            }
        }

    }
    init_invariant(spec, Self::init(), Self::next(), invariant);
}

}

}
