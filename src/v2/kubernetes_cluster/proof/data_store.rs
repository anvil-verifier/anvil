// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::v2::kubernetes_cluster::spec::{
    api_server::state_machine::unmarshallable_object, cluster_state_machine::*, message::*,
};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn valid_builtin_object(obj: DynamicObjectView) -> bool {
    if obj.kind == ConfigMapView::kind() { ConfigMapView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == DaemonSetView::kind() { DaemonSetView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == PersistentVolumeClaimView::kind() { PersistentVolumeClaimView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == PodView::kind() { PodView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == RoleBindingView::kind() { RoleBindingView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == RoleView::kind() { RoleView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == SecretView::kind() { SecretView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == ServiceView::kind() { ServiceView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == StatefulSetView::kind() { StatefulSetView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == ServiceAccountView::kind() { ServiceAccountView::unmarshal(obj).get_Ok_0().state_validation() }
    else { true }
}

pub open spec fn etcd_object_is_well_formed(self, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[key];
        &&& obj.metadata.well_formed()
        &&& obj.object_ref() == key
        &&& obj.metadata.resource_version.get_Some_0() < s.api_server.resource_version_counter
        &&& obj.metadata.uid.get_Some_0() < s.api_server.uid_counter
        &&& unmarshallable_object(obj, self.installed_types)
        &&& Self::valid_builtin_object(obj)
    }
}

pub open spec fn each_object_in_etcd_is_well_formed(self) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
                ==> self.etcd_object_is_well_formed(key)(s)
    }
}

// #[verifier(spinoff_prover)]
// pub proof fn lemma_always_each_object_in_etcd_is_well_formed(self, spec: TempPred<ClusterState>)
//     requires
//         spec.entails(lift_state(self.init())),
//         spec.entails(always(lift_action(self.next()))),
//     ensures spec.entails(always(lift_state(self.each_object_in_etcd_is_well_formed()))),
// {
//     let invariant = self.each_object_in_etcd_is_well_formed();

//     assert forall |s, s_prime| invariant(s) && #[trigger] self.next()(s, s_prime) implies invariant(s_prime) by {
//         assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) implies self.etcd_object_is_well_formed(key)(s_prime) by {
//             ConfigMapView::marshal_status_preserves_integrity();
//             DaemonSetView::marshal_status_preserves_integrity();
//             PersistentVolumeClaimView::marshal_status_preserves_integrity();
//             PodView::marshal_status_preserves_integrity();
//             RoleBindingView::marshal_status_preserves_integrity();
//             RoleView::marshal_status_preserves_integrity();
//             SecretView::marshal_status_preserves_integrity();
//             ServiceView::marshal_status_preserves_integrity();
//             StatefulSetView::marshal_status_preserves_integrity();
//             ServiceAccountView::marshal_status_preserves_integrity();
//             // K::marshal_status_preserves_integrity();
//             if s.resources().contains_key(key) {
//                 let step = choose |step| self.next_step(s, s_prime, step);
//                 match step {
//                     Step::APIServerStep(input) => {
//                         match input.get_Some_0().content.get_APIRequest_0() {
//                             APIRequest::GetRequest(_) => {}
//                             APIRequest::ListRequest(_) => {}
//                             APIRequest::CreateRequest(_) => {}
//                             APIRequest::DeleteRequest(_) => {}
//                             APIRequest::UpdateRequest(_) => {}
//                             APIRequest::UpdateStatusRequest(_) => {}
//                         }
//                     }
//                     _ => {}
//                 }
//             } else {}
//         }
//     }

//     init_invariant(spec, self.init(), self.next(), invariant);
// }

}

}
