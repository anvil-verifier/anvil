// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

impl Cluster {

// This desired_state_is specifies what the desired state looks like (described in the cr object).
// Informally, it says that given the cr object, the object's key exists in the etcd,
// and the corresponding object in etcd has the same spec and uid of the given cr object.
//
// One way to interpret always(desired_state_is) is that the object that describes the desired state
// of the custom controller always exists in etcd, and its spec never changes (always the same as the input cr's spec).
//
// You might wonder why not just say that T::unmarshal(s.resources()[cr.object_ref()]).get_Ok_0() == cr?
// However, in this way, always(desired_state_is) then implies that the cr object never gets updated
// and its resource version remains unchanged, which is unnecessarily strong for most cases.
// We require the cr object's spec field to remain unchanged, but other fields, like status, could change.
pub open spec fn desired_state_is<T: CustomResourceView>(cr: T) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& cr.metadata().name.is_Some()
        &&& cr.metadata().namespace.is_Some()
        // The object that has the same key with cr exists in etcd...
        &&& s.resources().contains_key(cr.object_ref())
        // and its uid is the same as cr...
        &&& s.resources()[cr.object_ref()].metadata.uid == cr.metadata().uid
        // and can be unmarshalled to T...
        &&& T::unmarshal(s.resources()[cr.object_ref()]).is_Ok()
        // and its spec is the same as cr.
        &&& T::unmarshal(s.resources()[cr.object_ref()]).get_Ok_0().spec() == cr.spec()
    }
}

pub open spec fn eventually_stable_reconciliation<T: CustomResourceView>(current_state_matches: spec_fn(T) -> StatePred<ClusterState>) -> TempPred<ClusterState> {
    tla_forall(|cr: T| always(lift_state(Self::desired_state_is(cr))).leads_to(always(lift_state(current_state_matches(cr)))))
}

pub open spec fn eventually_stable_reconciliation_per_cr<T: CustomResourceView>(cr: T, current_state_matches: spec_fn(T) -> StatePred<ClusterState>) -> TempPred<ClusterState> {
    always(lift_state(Self::desired_state_is(cr))).leads_to(always(lift_state(current_state_matches(cr))))
}

}

}
